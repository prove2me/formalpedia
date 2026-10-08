-- Prove2me | Theorems.Thm_Helfgott_etaTwo_mass
-- name    : Helfgott.etaTwo_mass
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-04T21:25:51.057996+00:00
-- url     : https://prove2.me/theorems/9db6eb8b-91c2-4eda-8dd0-0a284de77908
-- title:
--   Exact unit mass of the logarithmic Goldbach smoothing
-- statement:
--   The nonnegative logarithmic smoothing η₂(t)=4 max(log2−|log(2t)|,0) for t>0, extended by zero for t≤0, has integral 1 over the real line. Its support lies in [1/4,1]. This is the normalization used for the common minor-arc smoothing in the Tao and Helfgott Goldbach arguments.
-- source:
--   H. A. Helfgott, The ternary Goldbach conjecture is true, arXiv:1312.7748v2, equations (4.7), (4.10) and (7.12), https://arxiv.org/html/1312.7748v2 . Written by Codex.

import Definitions.Def_Helfgott_Smoothings
open MeasureTheory

namespace Helfgott

theorem etaTwo_mass : (∫ t : ℝ, etaTwo t) = 1 := by sorry

end Helfgott
