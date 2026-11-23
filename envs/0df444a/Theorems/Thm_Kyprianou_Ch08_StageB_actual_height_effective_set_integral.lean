-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_actual_height_effective_set_integral
-- name    : Kyprianou.Ch08.StageB.actual_height_effective_set_integral
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T02:45:03.046157+00:00
-- url     : https://prove2.me/theorems/06e3eaa9-23fe-4b70-b7b7-e951a0a99ba3
-- title:
--   Actual-height no-drawdown integral equals its finite-clock effective-domain integral
-- statement:
--   For a spectrally negative model with Laplace exponent psi, a nonnegative level q, and positive barrier b and drawdown height h, the discounted no-drawdown set integral equals the same integral restricted to paths whose first strict upward passage clock is finite. The omitted infinite-clock part carries zero discounted payoff. The measurability of the finite-clock effective-domain event is an explicit premise so that the parent bridge can discharge it with the separate measurability child.
-- source:
--   Source-faithful Child B of pinned parent Kyprianou.Ch08.StageB.actual_height_semigroup [47fdba96-7849-46b6-87b0-6cea26c5eadd] at revision 0df444a360eaa60ab8c11dca51a86af692955474. Isolates the effective-domain reduction of the parent's original no-drawdown set integral: the infinite-clock part carries zero discounted payoff. The process, events, payoff, preamble, probability measure, exponent hypothesis and positivity assumptions are the parent's; the finite-clock event measurability is retained as an explicit premise for the separate parent bridge. Repairs: v1 [b2e879c1-75fc-455c-922f-7a22354c8688] failed because Set.setOf is not a pinned constant; v2 [1a6cfcc9-128f-467f-9dde-b2ae3128f81c] failed because the public twoSidedExitUpTime provider [a151e213-9af7-4401-b163-8e74db317cf8] takes SpectrallyNegativeLevy P 𝓕 and cannot accept the parent raw path D.X : ℝ≥0 → Ω → ℝ. The parent's own tauPlus D.X b clock is therefore used for the finite strict upward exit condition, preserving the parent process and payoff. The declaration is fully qualified so the generated target's self-reference resolves explicitly. No set-builder braces are used.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

theorem Kyprianou.Ch08.StageB.actual_height_effective_set_integral
    {Ω : Type} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P)
    (ψ : ℝ → ℝ)
    (hψ : IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ)
    (q : ℝ) (hq : 0 ≤ q)
    (b : ℝ) (hb : 0 < b)
    (h : ℝ) (hh : 0 < h)
    (hE : MeasurableSet (setOf (fun ω : Ω =>
      tauPlus D.X b ω < ⊤ ∧
        NoDrawdownBeforeUpcrossing D.X b h ω))) :
    (∫ ω in setOf (fun ω : Ω =>
        NoDrawdownBeforeUpcrossing D.X b h ω),
      Real.exp (Phi ψ q * b) * discountedAt q (tauPlus D.X b ω) ∂P) =
    (∫ ω in setOf (fun ω : Ω =>
        tauPlus D.X b ω < ⊤ ∧
          NoDrawdownBeforeUpcrossing D.X b h ω),
      Real.exp (Phi ψ q * b) * discountedAt q (tauPlus D.X b ω) ∂P) := by
  sorry
