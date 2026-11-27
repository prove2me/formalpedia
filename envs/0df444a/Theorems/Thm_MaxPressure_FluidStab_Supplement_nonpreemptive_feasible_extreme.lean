-- Prove2me | Theorems.Thm_MaxPressure_FluidStab_Supplement_nonpreemptive_feasible_extreme
-- name    : MaxPressure.FluidStab.Supplement.nonpreemptive_feasible_extreme
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T08:17:34.801042+00:00
-- url     : https://prove2.me/theorems/f6738cef-f180-4e14-84c0-f6d4481c2cb1
-- title:
--   Lemma 2 (corrected: finite rates) — nonpreemptive feasible extremes exist
-- statement:
--   In a reversed Leontief network, each activity requires exactly one processor. Let $s$ be any physical decision snapshot with nonnegative buffer contents, compatible unfinished processor commitments, and enough buffer jobs for the unfinished activities it holds. Then
--
--   $$\mathcal E\cap\mathcal A_{\mathrm{np}}(s)\ne\varnothing.$$
--
--   Here $\mathcal A_{\mathrm{np}}(s)$ preserves every unfinished input or service activity at level one, reserves its held constituent jobs, and supplies fresh jobs to new activities. This applies at every time along a legal nonpreemptive history, including initial and simultaneous-completion decisions. Nonemptiness is the conclusion; neither a current allocation nor policy existence is assumed. No EAA, moment law, SAP or load slack is assumed.
--
--   Differences from the source:
--   - correction: The page permits nonnegative mean requirements and presupposes input processors can work. → The published Standing predicate requires positive means and an activity at each input processor.; reason: These are the inherited disclosed finite-rate and nonidling conventions; zero mean rates and unused input processors are excluded.
--   - encoding: Feasible extremes at each time along a legal nonpreemptive history. → The same physical feasible-extreme set evaluated at an arbitrary snapshot carrying the physical invariants.; reason: Snapshot formation from a legal history supplies these invariants, with unfinished input activities retained.
--   - generalization: Decision states reached along nonpreemptive maximum-pressure histories. → Every snapshot satisfying only processor compatibility, held-job availability and nonnegative contents.; reason: Existence is geometric and does not require reachability or pressure maximization.
-- source:
--   Dai & Lin, Maximum pressure policies in stochastic processing networks, Oper. Res. 53(2) (2005), p. 207, Lemma 2; https://doi.org/10.1287/opre.1040.0170

import Mathlib
import Definitions.Def_MaxPressure_FluidStab_Supplement_Allocations

namespace MaxPressure.FluidStab.Supplement

open MeasureTheory Filter Topology

theorem nonpreemptive_feasible_extreme
    {I J K : ℕ} (N : FluidStab.Network I J K)
    (hN : N.Standing) (hrev : ReversedLeontief.IsReversedLeontief (reversedNetwork N))
    (s : Snapshot I J) (hphysical : s.Legal N) :
    (feasibleExtremes N s).Nonempty := by sorry

end MaxPressure.FluidStab.Supplement
