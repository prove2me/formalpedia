-- Prove2me | Theorems.Thm_MultiItemRev_BundlingOpt_display_18
-- name    : MultiItemRev.BundlingOpt.display_18
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T20:25:48.862021+00:00
-- url     : https://prove2.me/theorems/2a32fe38-8af3-45e1-9300-5cf61c29e36a
-- title:
--   (18), p. 45 — for symmetric IC µ, b(y, z) ≤ b(y + z − a, a) = b̂(y, z) on [a, ∞)²
-- statement:
--   Let $\mu = (q,s)$ be an incentive-compatible symmetric two-good mechanism with buyer payoff $b$, and let $a \ge 0$. Then for every $(y, z)$ with $y, z \ge a$,
--   $$b(y, z) \ \le\ b(y + z - a,\ a) = \hat b(y,z).$$
--
--   The point $(y,z)$ lies on the segment between $(y+z-a, a)$ and $(a, y+z-a)$, at which $b$ takes the same value by symmetry. This inequality says that the bundled payoff $\hat b$ majorizes $b$ on the quadrant $[a,\infty)^2$, which is the key comparison in the proof of Theorem 16.
--
--   **Formalization Note** Only incentive compatibility (which gives convexity of $b$) and symmetry are assumed. Valuations are in $\mathbb{R}_{\ge0}$, and $y + z - a \ge a$ under the hypotheses, so the subtraction is exact.
-- source:
--   Hart and Nisan, Approximate Revenue Maximization with Multiple Items, arXiv:1204.1846v3, p. 45, proof of Theorem 16, display (18)

import Mathlib
import Definitions.Def_MultiItemRev_BundlingOpt_Model
import Definitions.Def_MultiItemRev_BundlingOpt_Bundling
open MeasureTheory
open scoped NNReal ENNReal

namespace MultiItemRev.BundlingOpt

theorem display_18 (M : Mechanism (Fin 2)) (hIC : IsIC M) (hsym : IsSymmetric M)
    (a y z : ℝ≥0) (hy : a ≤ y) (hz : a ≤ z) :
    buyerPayoff M ![y, z] ≤ buyerPayoff M ![y + z - a, a] := by sorry

end MultiItemRev.BundlingOpt
