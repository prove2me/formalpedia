-- Prove2me | Theorems.Thm_Garrido_not_exists_invariant_measure_closedBall
-- name    : Garrido.not_exists_invariant_measure_closedBall
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-24T14:04:06.540127+00:00
-- url     : https://prove2.me/theorems/30cae3de-2a09-42d6-a1d5-f4638dc1995e
-- title:
--   p. 1 — no isometry-invariant finitely additive measure on ℝ³ gives the unit ball a finite nonzero value
-- statement:
--   There is no finitely additive measure $m : \mathcal{P}(\mathbb{R}^3) \to [0,\infty]$,
--   defined on every subset of $\mathbb{R}^3$ and invariant under all isometries, that gives the
--   closed unit ball $\mathbb{B}$ a finite nonzero measure:
--
--   $$\nexists\, m \ \text{finitely additive, isometry-invariant, with } 0 < m(\mathbb{B}) < \infty.$$
--
--   This is the form of the Banach–Tarski paradox that says Lebesgue measure cannot be extended to
--   all subsets of $\mathbb{R}^3$ as an isometry-invariant finitely additive measure.
--
--   **Formalization Note.** The source asks only that the ball have nonzero measure; that version is
--   false, because the measure giving every nonempty set the value $\infty$ is finitely additive
--   and isometry-invariant. The statement therefore also requires the value to be finite. The ball
--   is the closed ball of radius $1$ about the origin, and the isometries are the imported
--   `EuclideanGroup 3`.
-- source:
--   A. Garrido, "An introduction to amenable groups", lecture notes, Oxford Advanced Class in Algebra, Michaelmas 2013 (PDF, Feb 2015), p. 1, the introduction to Section 1.1. The source says "non-zero measure"; the statement requires a finite nonzero value, since the measure that is infinite on every nonempty set is isometry-invariant and finitely additive; https://web.archive.org/web/20260805000803/https://www.math.uni-duesseldorf.de/~garrido/amenable.pdf

import Mathlib
import Definitions.Def_Garrido_BanachTarski
import Definitions.Def_Garrido_Amenability
open scoped ENNReal

namespace Garrido

theorem not_exists_invariant_measure_closedBall :
    ¬ ∃ m : Set (EuclideanSpace ℝ (Fin 3)) → ℝ≥0∞, IsFinitelyAdditiveMeasure m ∧
      IsInvariant (EuclideanGroup 3) m ∧
      m (Metric.closedBall 0 1) ≠ 0 ∧ m (Metric.closedBall 0 1) ≠ ⊤ := by
  sorry

end Garrido
