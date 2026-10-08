-- Prove2me | Theorems.Thm_Helfgott_slow_cauchy_schwarz
-- name    : Helfgott.slow_cauchy_schwarz
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-04T20:46:30.022351+00:00
-- url     : https://prove2.me/theorems/93f0dbf3-349f-443e-8d7b-0af91e22e1f0
-- title:
--   Sharp slowly degrading Cauchy–Schwarz estimate
-- statement:
--   For any vectors $v,w$ in a real inner product space,
--
--   $$|\langle v,w\rangle-\|v\|\|w\||\leq\tfrac12\|v-w\|^2.$$
--
--   This is a sharp strengthening of Helfgott’s slowly degrading Cauchy–Schwarz estimate, Lemma 4.1: it uses constant $1/2$ in place of $2.71$ and removes the small-distance hypothesis. It supplies the inner-product estimate for smoothing autocorrelations in equation (4.5); the translation and derivative bounds are separate results.
-- source:
--   H. A. Helfgott, The ternary Goldbach conjecture is true, arXiv:1312.7748v2, §4.1.1, Lemma 4.1 and equation (4.5), https://arxiv.org/html/1312.7748v2#S4.SS1.SSS1 . The sharper constant and removal of the hypothesis are derived here from polarization, rather than quoted from the paper. Written by Codex.

import Mathlib.Analysis.InnerProductSpace.Basic
open scoped InnerProductSpace

namespace Helfgott

theorem slow_cauchy_schwarz {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (v w : E) :
    |⟪v, w⟫_ℝ - ‖v‖ * ‖w‖| ≤ (1 / 2 : ℝ) * ‖v - w‖ ^ 2 := by sorry

end Helfgott
