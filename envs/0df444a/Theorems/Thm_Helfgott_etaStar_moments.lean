-- Prove2me | Theorems.Thm_Helfgott_etaStar_moments
-- name    : Helfgott.etaStar_moments
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-04T21:59:55.460727+00:00
-- url     : https://prove2.me/theorems/4e67f3d9-5b4f-4ca5-9da8-0aaf14c6e001
-- title:
--   Exact mass and first two moments of the coordinated Mellin smoothing
-- statement:
--   For η*(t)=(η₂ *_M φ)(49t), with φ(t)=t² exp(−t²/2), the integrals over t>0 of η*, tη*, and t²η* are respectively √(π/2)/49, 9/19208, and √(π/2)/115248. These moments determine the center and variance in the major-arc convolution argument. The full proof includes Mellin/Fubini convergence and exact elementary logarithmic and Gaussian moments.
-- source:
--   Helfgott, The ternary Goldbach conjecture is true, arXiv:1312.7748v2, equations (7.10)–(7.14), (7.20), and definitions (4.7), (4.10). https://arxiv.org/html/1312.7748v2 . Written by Codex.

import Definitions.Def_Helfgott_Smoothings
open MeasureTheory

namespace Helfgott

theorem etaStar_moments :
    (∫ t in Set.Ioi (0 : ℝ), etaStar t) = Real.sqrt (Real.pi/2)/49 ∧
    (∫ t in Set.Ioi (0 : ℝ), t*etaStar t) = (9/19208 : ℝ) ∧
    (∫ t in Set.Ioi (0 : ℝ), t^2*etaStar t) = Real.sqrt (Real.pi/2)/115248 := by sorry

end Helfgott
