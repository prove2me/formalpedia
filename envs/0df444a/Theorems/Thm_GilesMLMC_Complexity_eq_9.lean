-- Prove2me | Theorems.Thm_GilesMLMC_Complexity_eq_9
-- name    : GilesMLMC.Complexity.eq_9
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:22:39.254923+00:00
-- url     : https://prove2.me/theorems/8f10377a-a100-425a-b854-a8f685b57fc2
-- title:
--   (9) — $\sum_{l=0}^Lh_l^{-(1-\beta)/2}<h_L^{-(1-\beta)/2}(1-M^{-(1-\beta)/2})^{-1}$ for $\beta<1$
-- statement:
--   Let $M\ge2$ be an integer, $T>0$, $\beta<1$, $h_l=M^{-l}T$ and $L\ge0$. Then
--   $$\sum_{l=0}^{L}h_l^{-(1-\beta)/2}=h_L^{-(1-\beta)/2}\sum_{l=0}^{L}\big(M^{-(1-\beta)/2}\big)^l<h_L^{-(1-\beta)/2}\big(1-M^{-(1-\beta)/2}\big)^{-1}.$$
--
--   The sum is dominated by its finest-level term, up to a constant factor independent of $L$.
--
--   **Formalization Note** Only the outer strict inequality is stated; the middle equality reindexes $l\mapsto L-l$. Powers with real exponents are real powers.
-- source:
--   Giles, Multilevel Monte Carlo path simulation, Operations Research 56(3) (2008), §3, proof of Theorem 3.1, case (c), (9), p. 610

import Mathlib
import Definitions.Def_GilesMLMC_Complexity_Setup

namespace GilesMLMC.Complexity

/-- Inequality (9) (Giles 2008, §3, proof of Theorem 3.1, case (c), p. 610, PDF 4, right column, top): for `β < 1`, `Σ_{l=0}^L h_l^{−(1−β)/2} = h_L^{−(1−β)/2} Σ_{l=0}^L (M^{−(1−β)/2})^l < h_L^{−(1−β)/2}(1 − M^{−(1−β)/2})⁻¹`.

Formalization Note. Only the outer strict inequality is stated (the middle equality reindexes `l ↦ L − l`). Powers with real exponents are `Real.rpow`. It holds for every `L : ℕ`. -/
theorem eq_9
    (M : ℕ) (hM : 2 ≤ M) (T : ℝ) (hT : 0 < T)
    (β : ℝ) (hβ : β < 1) (L : ℕ) :
    ∑ l ∈ Finset.range (L + 1), h M T l ^ (-(1 - β) / 2) <
      h M T L ^ (-(1 - β) / 2) * (1 - (M : ℝ) ^ (-(1 - β) / 2))⁻¹ := by sorry

end GilesMLMC.Complexity
