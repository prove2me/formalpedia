-- Prove2me | Theorems.Thm_LpSubspaceCoreset_SmallP_lemma_A_2
-- name    : LpSubspaceCoreset.SmallP.lemma_A_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T01:47:56.471007+00:00
-- url     : https://prove2.me/theorems/6e5f977b-a2ef-4889-916e-99ee5e0ab07f
-- title:
--   Lemma A.2 — duality-map entropy
-- statement:
--   Let $r,M\ge1$, $B\ge0$, $H$ a real Hilbert space, $\nu$ a probability law supported on at most $M$ indices, $y_i\in\mathbb R^r$, $\alpha_i\ge0$, $z_i\in H$ with $\|z_i\|\le B$, and $\mathcal A$ a nonempty family of linear maps $\mathbb R^r\to H$. Fix $1\le p\le2$ and put $h_A(i)=p\langle J_p(\alpha_iAy_i),z_i\rangle$.
--
--   If $1<p\le2$ and the empirical $p$-energy $E_\nu=\sup_{A\in\mathcal A}\sum_i\nu_i\|\alpha_iAy_i\|^p$ is finite, then for every $\delta>0$
--   $$\log N(\delta,\{h_A\},L_2(\nu))\le C\,r\,E_\nu^{2-2/p}\delta^{-2}\big(\log(M+r+2)+\log(1+1/\delta)+\log(1+E_\nu)+1\big)^{C}\qquad(A.2)$$
--   and $\sup_A\|h_A\|_{L_2(\nu)}\le C\,E_\nu^{1-1/p}$ (A.3), with $C=C_{p,B}$ depending only on $p$ and $B$. At $p=1$ the entropy is at most $C\,r\,\delta^{-2}(\log(M+r+2)+\log(1+1/\delta)+1)^{C}$ for every $\delta>0$ and the radius is at most $C_0B$ for an absolute $C_0$.
--
--   These entropy bounds do not depend on the dimension of $H$; they control the duality-map coordinate of the loss in Theorem 3.1.
--
--   Differences from the source:
--   - reading: Õ_{p,B}(X), "the logarithms depend only on M + r + 2, 1 + 1/δ, and 1 + E_ν" → C·X·(log(M + r + 2) + log(1 + 1/δ) + log(1 + E_ν) + 1)^C with C = C_{p,B}; at p = 1 the same without the E_ν term; reason: polylogarithmic factors in exactly the quantities the statement names
--   - reading: radius O(B) at p = 1 → ≤ C₀·B with C₀ absolute (chosen before p and B); reason: O(·) with an absolute constant
--   - encoding: log N(δ, {h_A}, L2(ν)) ≤ X → some finite internal δ-cover 𝒩 ⊆ {h_A} has log |𝒩| ≤ X; reason: equivalent to the covering-number bound; avoids an infinite covering number becoming 0
--   - encoding: ν supported on at most M indices; E_ν < ∞ → ν a probability law on a finite index type with at most M nonzero weights; BddAbove of the energy set, E_ν its sSup; reason: only the support of ν matters; finiteness of the supremum is boundedness of the set
--   - encoding: a real Hilbert space H → H : Type with InnerProductSpace ℝ H and CompleteSpace H; reason: Lean's real Hilbert space
-- source:
--   Lin, Mirrokni, Woodruff, Nearly Optimal Strong Coresets for ℓp Subspace Approximation, arXiv:2608.26047 (held PDF of 2026-11-03, sha256 4c61606e…), p. 37, Lemma A.2

import Mathlib
import Definitions.Def_LpSubspaceCoreset_SmallP_Process

namespace LpSubspaceCoreset.SmallP

open scoped InnerProductSpace

/-- **Lemma A.2** (Duality-map entropy), p. 37.

Let `r, M ≥ 1`, `B ≥ 0`, `H` a real Hilbert space, `ν` a probability law on a finite index set
supported on at most `M` indices, `y_i ∈ ℝ^r`, `α_i ≥ 0`, `z_i ∈ H` with `‖z_i‖ ≤ B`, and `𝒜` a
nonempty family of linear maps `ℝ^r → H`. Fix `1 ≤ p ≤ 2` and put `h_A(i) = p⟨J_p(α_i A y_i), z_i⟩`.
* If `1 < p ≤ 2` and `E_ν = sup_{A∈𝒜} Σ_i ν_i ‖α_i A y_i‖^p < ∞`, then for every `δ > 0` some
  internal `δ`-cover `𝒩` of `{h_A}` in `L2(ν)` has
  `log |𝒩| ≤ C r E_ν^{2−2/p} δ^{−2} (log(M + r + 2) + log(1 + 1/δ) + log(1 + E_ν) + 1)^C` (A.2),
  and `sup_A ‖h_A‖_{L2(ν)} ≤ C E_ν^{1−1/p}` (A.3), with `C = C_{p,B}`.
* At `p = 1`: for every `δ > 0` some cover has
  `log |𝒩| ≤ C r δ^{−2} (log(M + r + 2) + log(1 + 1/δ) + 1)^C` (`Õ_B(rδ^{−2})`), and the radius is at
  most `C₀ B` with an absolute constant `C₀` (`O(B)`). -/
theorem lemma_A_2 :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧
    ∀ p : ℝ, 1 ≤ p → p ≤ 2 → ∀ B : ℝ, 0 ≤ B → ∃ C : ℝ, 0 ≤ C ∧
    ∀ (r M : ℕ), 1 ≤ r → 1 ≤ M →
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
      (ι : Type) [Fintype ι] (ν : ι → ℝ), IsProbLaw ν →
      (Finset.univ.filter fun i => ν i ≠ 0).card ≤ M →
    ∀ (y : ι → EuclideanSpace ℝ (Fin r)) (α : ι → ℝ) (z : ι → H),
      (∀ i, 0 ≤ α i) → (∀ i, ‖z i‖ ≤ B) →
    ∀ 𝒜 : Set (EuclideanSpace ℝ (Fin r) →ₗ[ℝ] H), 𝒜.Nonempty →
      let h : (EuclideanSpace ℝ (Fin r) →ₗ[ℝ] H) → ι → ℝ :=
        fun T i => p * ⟪dualityMap p (α i • T (y i)), z i⟫_ℝ
      let energy : Set ℝ := {e | ∃ T ∈ 𝒜, e = ∑ i, ν i * ‖α i • T (y i)‖ ^ p}
      (1 < p → BddAbove energy →
        (∀ δ : ℝ, 0 < δ → ∃ 𝒩 : Finset (ι → ℝ), IsCover ν δ (h '' 𝒜) 𝒩 ∧
          Real.log 𝒩.card ≤ C * r * (sSup energy) ^ (2 - 2 / p) / δ ^ 2 *
            (Real.log (M + r + 2) + Real.log (1 + 1 / δ) + Real.log (1 + sSup energy) + 1) ^ C) ∧
        (∀ T ∈ 𝒜, l2Dist ν (h T) 0 ≤ C * (sSup energy) ^ (1 - 1 / p))) ∧
      (p = 1 →
        (∀ δ : ℝ, 0 < δ → ∃ 𝒩 : Finset (ι → ℝ), IsCover ν δ (h '' 𝒜) 𝒩 ∧
          Real.log 𝒩.card ≤ C * r / δ ^ 2 *
            (Real.log (M + r + 2) + Real.log (1 + 1 / δ) + 1) ^ C) ∧
        (∀ T ∈ 𝒜, l2Dist ν (h T) 0 ≤ C₀ * B)) := by sorry

end LpSubspaceCoreset.SmallP
