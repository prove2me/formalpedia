-- Prove2me | Theorems.Thm_LogSupermodularBIS_Main_theorem_5_3
-- name    : LogSupermodularBIS.Main.theorem_5_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:34:45.371199+00:00
-- url     : https://prove2.me/theorems/6fb4b3c5-1c58-4f7f-9d5c-329fac3b8074
-- title:
--   Theorem 5.3 — near-optimal guides with small high-degree tails
-- statement:
--   Let $\Phi$ be a normalized supermodular potential on $d$ coordinates. For every $0<w\le1/2$ there is a guide $g$ such that
--   1. (near-optimal objective value) $0\le\log Z_\Phi-\mathcal P(g)\le dw^2/4$, and
--   2. (low-degree approximation) $\|\Pi_{>D}g_i\|_2\le\tfrac12(1-w/2)^{(D+1)/2}$ for every row $i$ and every integer $D\ge0$.
--
--   Differences from the source: none.
-- source:
--   Jingcheng Liu, Yitong Yin, STOC 2027 submission #1385 (October 2026), p. 26 (PDF 27), Theorem 5.3

import Definitions.Def_LogSupermodularBIS_Main_Smoothing

open MeasureTheory

set_option autoImplicit false

namespace LogSupermodularBIS.Main

/-- Theorem 5.3 (Near-optimal guides with small high-degree tails), p. 26. -/
theorem theorem_5_3 {d : ℕ} (Φ : (Fin d → Bool) → ℝ) (hΦ₀ : Φ (zeroConfig d) = 0)
    (hsup : Supermodular Φ) (w : ℝ) (hw : w ∈ Set.Ioc (0 : ℝ) (1 / 2)) :
    ∃ g : (Fin d → ℝ) → Fin d → ℝ, IsGuide d g ∧
      0 ≤ Real.log (potentialPartition Φ) - variationalObjective Φ g ∧
      Real.log (potentialPartition Φ) - variationalObjective Φ g ≤ d * w ^ 2 / 4 ∧
      ∀ i : Fin d, ∀ D : ℕ, l2Norm (highDegreeTail D fun u => g u i) ≤
        (1 / 2) * (1 - w / 2) ^ (((D : ℝ) + 1) / 2) := by sorry

end LogSupermodularBIS.Main
