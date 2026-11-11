-- Prove2me | Theorems.Thm_LpSubspaceCoreset_SmallP_corollary_A_3
-- name    : LpSubspaceCoreset.SmallP.corollary_A_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T01:48:03.528859+00:00
-- url     : https://prove2.me/theorems/b92db384-86fd-485c-966d-3a6f4a685ff5
-- title:
--   Corollary A.3 — conditional duality-map complexity
-- statement:
--   In the setting of Lemma A.2 let $\nu=m^{-1}\sum_{s=1}^m\delta_{I_s}$ be the empirical law of sampled indices $I_1,\dots,I_m$ ($m\ge1$). Conditionally on the sample, with $C=C_{p,B}$,
--   $$R^{\mathrm{abs}}_m(\{h_A\}\mid I_1,\dots,I_m)\le C\big(E_\nu^{1-1/p}+E_\nu^{(1-1/p)/2}\big)\sqrt{r/m}\,\big(\log(m+r+2)+\log(1+E_\nu)+1\big)^{C}$$
--   for $1<p\le2$ (with $E_\nu<\infty$), and $R^{\mathrm{abs}}_m(\{h_A\}\mid I_1,\dots,I_m)\le C\sqrt{r/m}\,(\log(m+r+2)+1)^{C}$ for $p=1$.
--
--   It is the form in which Lemma A.2 enters the symmetrization step of Theorem 3.1.
--
--   Differences from the source:
--   - reading: Õ_{p,B}(·) → C·(·)·(log(m + r + 2) + log(1 + E_ν) + 1)^C with C = C_{p,B}; at p = 1 without the E_ν term; reason: Õ suppresses logarithmic factors in the relevant parameters (support size ≤ m, rank r, energy E_ν, as in Lemma A.2)
--   - encoding: R^abs_m(· | I_1, …, I_m) → radAbsCond, the average over the 2^m sign vectors of a supremum taken in [0, ∞]; reason: a finite expectation; no junk value for unbounded classes
--   - encoding: an empirical law m^{-1} Σ δ_{I_s} → 1 ≤ m and I : Fin m → ι on a finite index type; reason: an empirical law needs at least one sample
-- source:
--   Lin, Mirrokni, Woodruff, Nearly Optimal Strong Coresets for ℓp Subspace Approximation, arXiv:2608.26047 (held PDF of 2026-11-03, sha256 4c61606e…), p. 39, Corollary A.3

import Mathlib
import Definitions.Def_LpSubspaceCoreset_SmallP_Process

namespace LpSubspaceCoreset.SmallP

open scoped InnerProductSpace

/-- **Corollary A.3** (Conditional duality-map complexity), p. 39.

In the setting of Lemma A.2 with `ν = m^{−1} Σ_{s=1}^m δ_{I_s}` the empirical law of a sample
`I_1, …, I_m` (`m ≥ 1`), conditionally on the sampled indices,
`R^abs_m({h_A} | I_1, …, I_m) ≤ C (E_ν^{1−1/p} + E_ν^{(1−1/p)/2}) √(r/m) (log(m + r + 2) + log(1 + E_ν) + 1)^C`
for `1 < p ≤ 2` (with `E_ν < ∞`), and `≤ C √(r/m) (log(m + r + 2) + 1)^C` for `p = 1`, with
`C = C_{p,B}`. -/
theorem corollary_A_3 :
    ∀ p : ℝ, 1 ≤ p → p ≤ 2 → ∀ B : ℝ, 0 ≤ B → ∃ C : ℝ, 0 ≤ C ∧
    ∀ (r m : ℕ), 1 ≤ r → 1 ≤ m →
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
      (ι : Type) [Fintype ι] [DecidableEq ι] (I : Fin m → ι),
    ∀ (y : ι → EuclideanSpace ℝ (Fin r)) (α : ι → ℝ) (z : ι → H),
      (∀ i, 0 ≤ α i) → (∀ i, ‖z i‖ ≤ B) →
    ∀ 𝒜 : Set (EuclideanSpace ℝ (Fin r) →ₗ[ℝ] H), 𝒜.Nonempty →
      let h : (EuclideanSpace ℝ (Fin r) →ₗ[ℝ] H) → ι → ℝ :=
        fun T i => p * ⟪dualityMap p (α i • T (y i)), z i⟫_ℝ
      let energy : Set ℝ :=
        {e | ∃ T ∈ 𝒜, e = ∑ i, empiricalLaw I i * ‖α i • T (y i)‖ ^ p}
      (1 < p → BddAbove energy →
        radAbsCond (h '' 𝒜) I ≤ ENNReal.ofReal
          (C * ((sSup energy) ^ (1 - 1 / p) + (sSup energy) ^ ((1 - 1 / p) / 2)) *
            Real.sqrt (r / m) *
            (Real.log (m + r + 2) + Real.log (1 + sSup energy) + 1) ^ C)) ∧
      (p = 1 →
        radAbsCond (h '' 𝒜) I ≤ ENNReal.ofReal
          (C * Real.sqrt (r / m) * (Real.log (m + r + 2) + 1) ^ C)) := by sorry

end LpSubspaceCoreset.SmallP
