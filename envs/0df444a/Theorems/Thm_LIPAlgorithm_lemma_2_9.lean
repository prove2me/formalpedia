-- Prove2me | Theorems.Thm_LIPAlgorithm_lemma_2_9
-- name    : LIPAlgorithm.lemma_2_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T15:54:56.332211+00:00
-- url     : https://prove2.me/theorems/71b207ff-3439-4663-81fb-b9e9d199cffe
-- title:
--   Lemma 2.9 — section/quotient recursion
-- statement:
--   Let $L\subset\mathbb R^n$ be an integral full-rank lattice that is not well-rounded. Set $V=\mathrm{span}(\mathrm{Min}(L))$, $A=L\cap V$ and $Q=\pi_{V^\perp}(L)$. Then $A$ and $Q$ are lattices of ranks $\dim V$ and $n-\dim V$, and the following hold.
--
--   1. **Reconstruction.** The map $\tau_L:Q\to D(A)=A^*/A$, $\tau_L(q)=\pi_V(x)+A$ for any lift $x\in L$ of $q$, is a well-defined group homomorphism, and
--   $$L=\{a+u(q)+q:a\in A,\ q\in Q\},$$
--   where $u(q)\in A^*$ is any representative of $\tau_L(q)$.
--   2. **Gluing.** If $L_1,L_2$ are integral and both not well-rounded, every isomorphism between them maps $V_1$ to $V_2$, and
--   $$\mathrm{Iso}(L_1,L_2)=\{O_A\oplus O_Q:O_A\in\mathrm{Iso}(A_1,A_2),\ O_Q\in\mathrm{Iso}(Q_1,Q_2),\ \overline{O_A}\circ\tau_{L_1}=\tau_{L_2}\circ O_Q\}.$$
--
--   This reduces a general instance to two instances of smaller rank, and it is the recursion of the general algorithm.
--
--   Differences from the source:
--   - encoding: A, Q are lattices → discrete ℤ-submodules of ℝⁿ with the stated ℤ-rank; reason: a lattice that is not of full rank is exactly such a subgroup
--   - encoding: O_A ∘ τ_{L₁} = τ_{L₂} ∘ O_Q on discriminant groups → GlueCompat, the same equation on lifts; reason: τ_L(q) = π_V(x) + A for any lift, and O_Q maps Q₁ onto Q₂, so a lift of O_Q q exists
-- source:
--   Aggarwal, Jiang, Li, Liu, An n^{n+o(n)}-Time Algorithm for the Lattice Isomorphism Problem, STOC 2027 submission (manuscript sha256 61ee52aa…), Lemma 2.9, pp.11–12

import Mathlib
import Definitions.Def_LIPAlgorithm_GlueCompat

namespace LIPAlgorithm

/-- **Lemma 2.9 (Section/quotient recursion).** Aggarwal, Jiang, Li, Liu, STOC 2027 submission (manuscript
sha256 61ee52aa…), Lemma 2.9, pp.11–12 (PDF pp.14–15).

For `L` integral and not well-rounded, `V = span(Min(L))`, `A = L ∩ V`, `Q = π_{V⊥}(L)`: `A`, `Q` are lattices of
ranks `dim V` and `n − dim V`. (i) `τ_L : Q → D(A)`, `τ_L(q) = π_V(x) + A` for any lift `x ∈ L` of `q`, is a well-defined
group homomorphism, and `L = {a + u(q) + q}` for any choice of representatives `u(q) ∈ A*` of `τ_L(q)`. (ii) If `L₁`, `L₂`
are both integral and not well-rounded, every isomorphism maps `V₁` to `V₂`, and `Iso(L₁, L₂)` is exactly the set of maps
`O_A ⊕ O_Q` with `O_A ∈ Iso(A₁, A₂)`, `O_Q ∈ Iso(Q₁, Q₂)` and `O_A ∘ τ_{L₁} = τ_{L₂} ∘ O_Q`.

**Formalization Note.** "Lattice" for `A`, `Q` is a discrete subgroup of the stated `ℤ`-rank. The existence of `τ` with
the stated values on every lift is the well-definedness claim. `O_A ⊕ O_Q` is the isometry of `ℝⁿ` acting as `O_A` on
`V₁` and as `O_Q` on `V₁⊥`, and the compatibility is `GlueCompat`. -/
theorem lemma_2_9 {n : ℕ} :
    (∀ (L : Submodule ℤ (E n)) [DiscreteTopology L] [IsZLattice ℝ L],
      IsIntegralLattice L → ¬ IsWellRounded L →
        DiscreteTopology (secA L) ∧
        Module.finrank ℤ (secA L) = Module.finrank ℝ (spanMin L) ∧
        DiscreteTopology (quotQ L) ∧
        Module.finrank ℤ (quotQ L) = n - Module.finrank ℝ (spanMin L) ∧
        (∀ x ∈ L, (spanMin L).starProjection x ∈ secDual L) ∧
        ∃ τ : quotQ L →+ discr L,
          (∀ (x : E n) (hx : (spanMin L).starProjection x ∈ secDual L) (q : quotQ L), x ∈ L →
            (q : E n) = (spanMin L)ᗮ.starProjection x →
              τ q = Submodule.Quotient.mk ⟨(spanMin L).starProjection x, hx⟩) ∧
          ∀ u : quotQ L → secDual L, (∀ q, Submodule.Quotient.mk (u q) = τ q) →
            (L : Set (E n)) =
              {y | ∃ a ∈ secA L, ∃ q : quotQ L, y = a + (u q : E n) + (q : E n)}) ∧
    (∀ (L₁ L₂ : Submodule ℤ (E n)) [DiscreteTopology L₁] [IsZLattice ℝ L₁]
        [DiscreteTopology L₂] [IsZLattice ℝ L₂],
      IsIntegralLattice L₁ → IsIntegralLattice L₂ → ¬ IsWellRounded L₁ → ¬ IsWellRounded L₂ →
        (∀ O ∈ isoLat L₁ L₂, (fun x => O x) '' (spanMin L₁ : Set (E n)) = (spanMin L₂ : Set (E n))) ∧
        ∀ O : E n ≃ₗᵢ[ℝ] E n, O ∈ isoLat L₁ L₂ ↔
          ∃ (OA : spanMin L₁ ≃ₗᵢ[ℝ] spanMin L₂) (OQ : ↥(spanMin L₁)ᗮ ≃ₗᵢ[ℝ] ↥(spanMin L₂)ᗮ),
            MapsOnto OA (secA L₁) (secA L₂) ∧ MapsOnto OQ (quotQ L₁) (quotQ L₂) ∧
            GlueCompat L₁ L₂ OA OQ ∧
            (∀ x : spanMin L₁, O x = ((OA x : spanMin L₂) : E n)) ∧
            ∀ y : ↥(spanMin L₁)ᗮ, O y = ((OQ y : ↥(spanMin L₂)ᗮ) : E n)) := by sorry

end LIPAlgorithm
