-- Prove2me | Theorems.Thm_KallMayerSLP_ICC_theorem_4_3
-- name    : KallMayerSLP.ICC.theorem_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:11:32.598078+00:00
-- url     : https://prove2.me/theorems/2f9f0965-0560-447b-81b4-e1c6a84bd061
-- title:
--   Theorem 4.3 — the joint integrated chance constraint is polyhedral for finite discrete $\xi$
-- statement:
--   Let $\xi$ have the finite discrete distribution (4.7), with $p_k>0$, $\sum_k p_k=1$, $T^k=T(\hat\xi^k)$, $h^k=h(\hat\xi^k)$, and let $\mathcal I=\{1,\dots,s\}$. For $\gamma\ge 0$, the set $\mathcal S_J(\gamma)=\{x\mid K_J(x)\le\gamma\}$ is polyhedral, and
--   $$
--   \{x\mid K_J(x)\le\gamma\}=\bigcap_{\mathcal K\subset\mathcal N}\ \bigcap_{l\in\mathcal I^{\mathcal K}}\Big\{x\ \Big|\ \sum_{k\in\mathcal K}p_k\big(t^k_{l_k}x-h^k_{l_k}\big)\le\gamma\Big\},
--   $$
--   where $\mathcal I^{\mathcal K}$ is the set of tuples $(l_k,\,k\in\mathcal K)$ with $l_k\in\mathcal I$, and $t^k_{l_k}$ is the $l_k$-th row of $T^k$.
--
--   The joint constraint is therefore a system of $(s+1)^N-1$ proper linear inequalities. This is the central fact that makes joint integrated chance constraints linear programming constraints for scenario models.
--
--   **Formalization Note** $K_J$ is the expectation against the law (4.7), not the sum (4.20) by definition. A tuple $l$ is a function `𝒦 → Fin s`, and the sum over $\mathcal K$ is the sum over the subtype `↥𝒦`. "Polyhedral" is the published `IsPolyhedron`.
--
--   Differences from the source:
--
--   - generalization: ξ with realizations in ℝʳ, T(ξ), h(ξ) affine in ξ (1.2) → Ξ any measurable space with measurable singletons, T, h arbitrary functions, atoms not required distinct; reason: the book says (1.2) is not used in the chapter; Ξ = ℝʳ with its Borel sets gives the book's case
--   - generalization: s > 1 (§4.1.2) → every s ≥ 1; reason: for s = 1 the statement is Theorem 4.1 for that one row
--   - encoding: 𝒦 ⊂ 𝒩 over subsets of {1, …, N} → 𝒦 : Finset (Fin N), all subsets including ∅ and the whole set; reason: the book includes 𝒦 = ∅ with empty sum 0 (p.153); 0-based indices; same instances
-- source:
--   Kall & Mayer, Stochastic Linear Programming (2005), Chapter 2, Theorem 4.3 and (4.24), p.157 (PDF 167)

import Mathlib
import Definitions.Def_VanderbeiLP_StrictComp_Polyhedron
import Definitions.Def_KallMayerSLP_ICC_KJ
import Definitions.Def_KallMayerSLP_ICC_discreteLaw

open MeasureTheory Matrix

namespace KallMayerSLP.ICC

/-- **Theorem 4.3 (joint integrated chance constraints, finite discrete distribution).**
Kall & Mayer, *Stochastic Linear Programming* (2005), Chapter 2, Theorem 4.3 and (4.24), p.157
(PDF 167). For `γ ≥ 0`, `S_J(γ) = {x | K_J(x) ≤ γ}` is a polyhedral set, and
`{x | K_J(x) ≤ γ} = ⋂_{𝒦 ⊂ 𝒩} ⋂_{l ∈ ℐ^𝒦} {x | Σ_{k∈𝒦} p_k (tᵏ_{l_k} x − hᵏ_{l_k}) ≤ γ}`,
where `ℐ = {1, …, s}`, `ℐ^𝒦 = {(l_k, k ∈ 𝒦) | l_k ∈ ℐ for all k ∈ 𝒦}`, and `tᵏ_{l_k}` is the
`l_k`-th row of `Tᵏ`.

**Formalization Note.** `ξ` has the law (4.7), `Tᵏ = T(ξ̂ᵏ)`, `hᵏ = h(ξ̂ᵏ)`. `K_J` is the expectation
against that law, not the sum (4.20) by definition. `𝒦` runs over all subsets of `𝒩` including `∅`.
`l : 𝒦 → Fin s` is the tuple `(l_k, k ∈ 𝒦)`, and the sum over `k ∈ 𝒦` is the sum over the subtype
`↥𝒦`. The book states the section for `s > 1`; the statement here covers every `s ≥ 1`.
`MeasurableSingletonClass Ξ` holds for the book's `Ξ ⊂ ℝʳ` with the Borel σ-algebra. -/
theorem theorem_4_3 {Ξ : Type*} [MeasurableSpace Ξ] [MeasurableSingletonClass Ξ] {N s n : ℕ}
    [Nonempty (Fin s)] (p : Fin N → ℝ) (ξhat : Fin N → Ξ) (hp : ∀ k, 0 < p k)
    (hsum : ∑ k, p k = 1) (T : Ξ → Matrix (Fin s) (Fin n) ℝ) (h : Ξ → Fin s → ℝ)
    (γ : ℝ) (hγ : 0 ≤ γ) :
    VanderbeiLP.StrictComp.IsPolyhedron {x | KJ (discreteLaw p ξhat) T h x ≤ γ} ∧
    {x | KJ (discreteLaw p ξhat) T h x ≤ γ} =
      ⋂ (𝒦 : Finset (Fin N)) (l : 𝒦 → Fin s),
        {x | ∑ k : 𝒦, p k * (T (ξhat k) (l k) ⬝ᵥ x - h (ξhat k) (l k)) ≤ γ} := by sorry

end KallMayerSLP.ICC
