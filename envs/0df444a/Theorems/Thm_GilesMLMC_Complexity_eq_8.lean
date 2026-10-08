-- Prove2me | Theorems.Thm_GilesMLMC_Complexity_eq_8
-- name    : GilesMLMC.Complexity.eq_8
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:22:39.943887+00:00
-- url     : https://prove2.me/theorems/21f29140-8697-4754-8273-7d83667e46b8
-- title:
--   (8) — $\sum_{l=0}^Lh_l^{(\beta-1)/2}<T^{(\beta-1)/2}(1-M^{-(\beta-1)/2})^{-1}$ for $\beta>1$
-- statement:
--   Let $M\ge2$ be an integer, $T>0$, $\beta>1$, $h_l=M^{-l}T$ and $L\ge0$. Then
--   $$\sum_{l=0}^{L}h_l^{(\beta-1)/2}=T^{(\beta-1)/2}\sum_{l=0}^{L}\big(M^{-(\beta-1)/2}\big)^l<T^{(\beta-1)/2}\big(1-M^{-(\beta-1)/2}\big)^{-1}.$$
--
--   The bound is uniform in $L$; it converts the variance and the cost of case (b) into bounds that do not grow with the number of levels.
--
--   **Formalization Note** Only the outer strict inequality is stated; the middle equality is the identity $h_l=M^{-l}T$. Powers with real exponents are real powers.
-- source:
--   Giles, Multilevel Monte Carlo path simulation, Operations Research 56(3) (2008), §3, proof of Theorem 3.1, case (b), (8), p. 610

import Mathlib
import Definitions.Def_GilesMLMC_Complexity_Setup

namespace GilesMLMC.Complexity

/-- Inequality (8) (Giles 2008, §3, proof of Theorem 3.1, case (b), p. 610, PDF 4, left column): for `β > 1`, `Σ_{l=0}^L h_l^{(β−1)/2} = T^{(β−1)/2} Σ_{l=0}^L (M^{−(β−1)/2})^l < T^{(β−1)/2}(1 − M^{−(β−1)/2})⁻¹`.

Formalization Note. Only the outer strict inequality is stated (the middle equality is the computation `h_l = T M^{-l}`). Powers with real exponents are `Real.rpow`. It holds for every `L : ℕ`. -/
theorem eq_8
    (M : ℕ) (hM : 2 ≤ M) (T : ℝ) (hT : 0 < T)
    (β : ℝ) (hβ : 1 < β) (L : ℕ) :
    ∑ l ∈ Finset.range (L + 1), h M T l ^ ((β - 1) / 2) <
      T ^ ((β - 1) / 2) * (1 - (M : ℝ) ^ (-(β - 1) / 2))⁻¹ := by sorry

end GilesMLMC.Complexity
