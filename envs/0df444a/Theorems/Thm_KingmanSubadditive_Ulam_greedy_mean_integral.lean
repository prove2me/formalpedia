-- Prove2me | Theorems.Thm_KingmanSubadditive_Ulam_greedy_mean_integral
-- name    : KingmanSubadditive.Ulam.greedy_mean_integral
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T11:45:41.962549+00:00
-- url     : https://prove2.me/theorems/04b49a86-558a-43e8-b98e-0be65e7fbfb9
-- title:
--   Proof of Theorem 8, p. 895 — the integral ∫₀^∞∫₀^∞ x e^{−½(x+y)²} dx dy equals (π/8)^½
-- statement:
--   The double integral satisfies
--   $$\int_0^\infty\!\!\int_0^\infty x\,e^{-\frac12(x+y)^2}\,dx\,dy=\Big(\frac{\pi}{8}\Big)^{1/2}.$$
--
--   In the proof of the lower bound of Theorem 8 this number is the mean of the increments of a greedy ascending path through a planar Poisson process of unit rate, which yields $c\ge(8/\pi)^{1/2}$.
--
--   **Formalization Note** Only the value of the integral is stated, as an iterated integral (inner in $x$, outer in $y$, both over $(0,\infty)$). The probabilistic claim that the increments are independent and identically distributed with this mean needs a planar Poisson process and is not formalized.
-- source:
--   Kingman, Subadditive ergodic theory, Ann. Probab. 1(6):883–899 (1973), DOI 10.1214/aop/1176996798, p. 895, §2.4, proof of Theorem 8

import Mathlib
import Definitions.Def_KingmanSubadditive_Ulam_Permutations

open MeasureTheory Set

namespace KingmanSubadditive.Ulam

/-- The double integral of the proof of Theorem 8 (Kingman, *Subadditive ergodic theory*, Ann.
Probab. 1(6):883–899 (1973), §2.4, proof of Theorem 8, p. 895):
`∫₀^∞ ∫₀^∞ x e^{−½(x+y)²} dx dy = (π/8)^½`.

**Formalization Note** Only the computation is stated; the paper's claim that this is the mean
of the i.i.d. increments `x_r − x_{r−1}` of a greedy path through a planar Poisson process is not
formalized. The integrand is non-negative and integrable on the quadrant, so the iterated Bochner
integrals are the honest Lebesgue integrals. -/
theorem greedy_mean_integral :
    ∫ y in Ioi (0 : ℝ), ∫ x in Ioi (0 : ℝ), x * Real.exp (-(x + y) ^ 2 / 2) =
      Real.sqrt (Real.pi / 8) := by sorry

end KingmanSubadditive.Ulam
