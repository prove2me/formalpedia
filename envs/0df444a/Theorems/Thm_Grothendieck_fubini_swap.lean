-- Prove2me | Theorems.Thm_Grothendieck_fubini_swap
-- name    : Grothendieck.fubini_swap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T04:53:32.686049+00:00
-- url     : https://prove2.me/theorems/46b59159-434b-416b-b1f4-69672ee6d0f2
-- title:
--   The Fubini step of Lemma 2.1, unconditionally
-- statement:
--   With $X,Y$ the two columns of a random $r\times2$ matrix and $\tau$ the correlation of each row's bivariate Gaussian,
--
--   $$
--   \int_W \mathrm{reducedIntegrand}_r(W)\,d(\texttt{reducedLaw}\;r\;\tau)
--   =\frac1\pi\int_{(0,\infty)^2}\Big(\int_W \langle X,Y\rangle\,(st)^{-1/2}e^{-(s\lVert X\rVert^2+t\lVert Y\rVert^2)}\,d(\texttt{reducedLaw}\;r\;\tau)\Big)ds\,dt,
--   $$
--
--   with no hypotheses at all: the interchange of the Gaussian integral over the random matrix with the two Laplace parameters, the step that turns Lemma 2.1's expectation into row-wise Gaussian integrals.
--
--   The integrability Fubini needs is supplied, not assumed: $\lvert\langle X,Y\rangle\rvert\le\lVert X\rVert\lVert Y\rVert$, the kernel's $(s,t)$-integral is exactly $\pi$ at every $W$, and the law of $W$ is a probability measure, so the triple integral of the absolute value is at most $\pi$ by Tonelli; integrability follows and the swap is legitimate.
--
--   **Formalization Note** `fubiniIntegrand` and `planeMeasure` are definitions of the node `Grothendieck_Fubini`.
-- source:
--   Briët, de Oliveira Filho, Vallentin, *Grothendieck inequalities for semidefinite programs with rank constraint*, Theory of Computing 10(4), 2014, pp. 77-105 — Lemma 2.1, pp. 84-87.

import Mathlib
import Definitions.Def_Grothendieck_Fubini

open MeasureTheory
open scoped BigOperators Real

namespace Grothendieck

/-- **The Fubini step of Lemma 2.1, unconditionally.** The rounding expectation equals `π⁻¹` times
the iterated integral, against the Laplace parameters, of the row-wise expectation. -/
theorem fubini_swap (r : ℕ) (τ : ℝ) :
    (∫ W, reducedIntegrand r W ∂(reducedLaw r τ))
      = Real.pi⁻¹ * ∫ p, (∫ W, fubiniIntegrand r W p ∂(reducedLaw r τ)) ∂planeMeasure := by sorry

end Grothendieck
