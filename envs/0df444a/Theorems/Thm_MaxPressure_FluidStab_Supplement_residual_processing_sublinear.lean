-- Prove2me | Theorems.Thm_MaxPressure_FluidStab_Supplement_residual_processing_sublinear
-- name    : MaxPressure.FluidStab.Supplement.residual_processing_sublinear
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T08:20:26.274855+00:00
-- url     : https://prove2.me/theorems/17154c21-86bb-45dc-aa42-486923a54054
-- title:
--   Lemma 6 — For every sample path satisfying (3) and (29), the activity residual processing time is o(t).
-- statement:
--   Fix an activity processing sequence $\eta(\ell)\ge0$, constants $m\ge0$, $\varepsilon>0$ and $m'>0$, and an actual processing clock $0\le T(t)\le t$. Assume the path satisfies (3) and (29):
--
--   $$\frac1n\sum_{\ell=1}^n\eta(\ell)\longrightarrow m,\qquad \frac1n\sum_{\ell=1}^n\eta(\ell)^{1+\varepsilon}\longrightarrow m'.$$
--
--   Let $\widehat\eta(t)$ be the actual unfinished requirement of the episode held at activity time $T(t)$, with value zero when idle. Then
--
--   $$\lim_{t\to\infty}\frac{\widehat\eta(t)}t=0.$$
--
--   The assertion is deterministic on every sample path satisfying the displayed laws. It needs no routing law, probability space, positive busy fraction or integer exponent. Applying it to a delayed primitive sequence includes arbitrary finite initial residuals. The activity clock need not diverge.
--
--   Differences from the source:
--   - reading: The proof calls the renewal count (16). → Partial sums and the actual held episode are used, with (38) the correct renewal-count anchor.; reason: Equation (16) is a fluid processor equation; p. 212 explicitly defines the renewal count in (38).
--   - encoding: The activity residual is evaluated at time t. → The remaining requirement is evaluated at actual processing time T(t), and is zero when idle.; reason: This distinguishes wall time from activity time and does not replace a residual by a whole service duration.
--   - generalization: An activity residual within a nonpreemptive network history. → Any nondecreasing processing clock bounded by wall time, including frozen and idle clocks and mean m=0.; reason: The positive finite power limit alone controls max partial-sum increments relative to total processing; a full network history is unnecessary.
-- source:
--   Dai & Lin, Maximum pressure policies in stochastic processing networks, Oper. Res. 53(2) (2005), p. 215, Lemma 6; https://doi.org/10.1287/opre.1040.0170

import Mathlib
import Definitions.Def_MaxPressure_FluidStab_Supplement_Residuals

namespace MaxPressure.FluidStab.Supplement

open MeasureTheory Filter Topology

theorem residual_processing_sublinear
    (η : ℕ → ℝ) (m ε m' : ℝ) (c : ResidualClock)
    (hm : 0 ≤ m) (hε : 0 < ε) (hm' : 0 < m')
    (hclock : c.Legal η)
    (hLLN : Tendsto (fun n : ℕ =>
      BellWilliams2001.ThresholdPolicy.partialSum η n / n) atTop (𝓝 m))
    (hpower : Tendsto (fun n : ℕ =>
      (∑ l ∈ Finset.Icc 1 n, (η l) ^ (1 + ε)) / n) atTop (𝓝 m')) :
    Tendsto (fun t : ℝ => residual η c t / t) atTop (𝓝 0) := by sorry

end MaxPressure.FluidStab.Supplement
