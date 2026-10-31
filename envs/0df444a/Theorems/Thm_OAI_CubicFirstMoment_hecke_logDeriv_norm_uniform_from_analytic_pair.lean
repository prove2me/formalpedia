-- Prove2me | Theorems.Thm_OAI_CubicFirstMoment_hecke_logDeriv_norm_uniform_from_analytic_pair
-- name    : OAI.CubicFirstMoment.hecke_logDeriv_norm_uniform_from_analytic_pair
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T04:53:09.773734+00:00
-- url     : https://prove2.me/theorems/9a022371-17fb-4bac-9db7-de1ef784cdb9
-- title:
--   OAI.CubicFirstMoment.hecke_logDeriv_norm_uniform_from_analytic_pair: intermediate lemma from OpenAI, An unconditional first moment for cubic Gauss sums (result family 023)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CubicFirstMoment.patterson_firstMoment`, `OAI.CubicFirstMoment.patterson_angularComparison` and `OAI.CubicFirstMoment.patterson_angularCancellation`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An unconditional first moment for cubic Gauss sums (result family 023)*, OpenAI Math Release, September 25, 2026, result family 23, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CubicFirstMoment.hecke_logDeriv_norm_uniform_from_analytic_pair` of [lean/OAI/NumberTheory/CubicMoment/Estimates/HeckeUniformLogDerivative.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/CubicMoment/Estimates/HeckeUniformLogDerivative.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CubicFirstMoment`):
--
--   ```lean
--   theorem hecke_logDeriv_norm_uniform_from_analytic_pair
--       {χ χdual χ2dual : EisensteinIdealExponent → ℂ} (hχ : ∀ ν, ‖χ ν‖ ≤ 1)
--       (hχ0 : χ 0=1) (hχadd : ∀ ν κ, χ (ν+κ)=χ ν*χ κ)
--       (hχdual : ∀ ν, ‖χdual ν‖ ≤ 1) (hχ2dual : ∀ ν, ‖χ2dual ν‖ ≤ 1)
--       {L Ldual L2 L2dual : ℂ → ℂ} (hL : Differentiable ℂ L) (hL2 : Differentiable ℂ L2)
--       (hs : ∀ s : ℂ, 1 < s.re → L s=normDirichletSeries χ idealExponentNorm s)
--       (hs2 : ∀ s : ℂ, 1 < s.re → L2 s=normDirichletSeries (fun ν => (χ ν)^2) idealExponentNorm s)
--       (hds : ∀ s : ℂ, 1 < s.re → Ldual s=normDirichletSeries χdual idealExponentNorm s)
--       (hds2 : ∀ s : ℂ, 1 < s.re → L2dual s=normDirichletSeries χ2dual idealExponentNorm s)
--       {A A2 k k2 u T : ℝ} {ε ε2 : ℂ}
--       (hA : 0 < A) (hA2 : 0 < A2) (hk : 0 ≤ k) (hk2 : 0 ≤ k2)
--       (hε : ‖ε‖ ≤ 1) (hε2 : ‖ε2‖ ≤ 1) (hu : 10 ≤ u)
--       (huA : A ≤ u) (huA2 : A2 ≤ u) (huk : k+7 ≤ u) (huk2 : k2+7 ≤ u)
--       (huT : 4+2*(T+3) ≤ u)
--       (hFE : HeckeFunctionalEquation A k ε L Ldual)
--       (hFE2 : HeckeFunctionalEquation A2 k2 ε2 L2 L2dual)
--       (hcomp : ShiftedCompletedHeckeFiniteOrder A k L)
--       (hcomp2 : ShiftedCompletedHeckeFiniteOrder A2 k2 L2)
--       {σ t : ℝ} (hσ : 1-heckeZeroFreeWidth u/2 ≤ σ) (hσ2 : σ ≤ 2) (ht : |t| ≤ T) :
--       ‖logDeriv L ((σ:ℂ)+(t:ℂ)*Complex.I)‖ ≤
--         heckeLogSquaredConstant*(1+Real.log u)^2
--   ```
--
--   **Definitions.** The statement is written with `OAI.CubicFirstMoment.EisensteinIdealExponent` and `OAI.CubicFirstMoment.EisensteinIdealPrime` (definitions bundle `OAIQ096A000` of this split); `OAI.CubicFirstMoment.normDirichletSeries` (definitions bundle `OAIQ096A002` of this split); `OAI.CubicFirstMoment.idealExponentNorm` (definitions bundle `OAIQ096A004` of this split); `OAI.CubicFirstMoment.HeckeFunctionalEquation` and `OAI.CubicFirstMoment.ShiftedCompletedHeckeFiniteOrder` (definitions bundle `OAIQ096A005` of this split); `OAI.CubicFirstMoment.heckeLogSquaredConstant` and `OAI.CubicFirstMoment.heckeZeroFreeWidth` (definitions bundle `OAIQ096A026` of this split).
--
--   **Used by.** The proofs of `OAI_CubicFirstMoment_hecke_dyadic_prime_bound_of_analytic_pair` and `OAI.CubicFirstMoment.kummerPrimeSiegelWalfisz_of_primitive` of this split import it.
-- source:
--   OpenAI, An unconditional first moment for cubic Gauss sums (result family 023), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 23; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-unconditional-first-moment-for-cubic-Gauss-sums-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/CubicMoment/Estimates/HeckeUniformLogDerivative.lean (declaration OAI.CubicFirstMoment.hecke_logDeriv_norm_uniform_from_analytic_pair)

import Mathlib
import Definitions.Def_OAIQ096A026

section

attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace CubicFirstMoment

theorem hecke_logDeriv_norm_uniform_from_analytic_pair
    {χ χdual χ2dual : EisensteinIdealExponent → ℂ} (hχ : ∀ ν, ‖χ ν‖ ≤ 1)
    (hχ0 : χ 0=1) (hχadd : ∀ ν κ, χ (ν+κ)=χ ν*χ κ)
    (hχdual : ∀ ν, ‖χdual ν‖ ≤ 1) (hχ2dual : ∀ ν, ‖χ2dual ν‖ ≤ 1)
    {L Ldual L2 L2dual : ℂ → ℂ} (hL : Differentiable ℂ L) (hL2 : Differentiable ℂ L2)
    (hs : ∀ s : ℂ, 1 < s.re → L s=normDirichletSeries χ idealExponentNorm s)
    (hs2 : ∀ s : ℂ, 1 < s.re → L2 s=normDirichletSeries (fun ν => (χ ν)^2) idealExponentNorm s)
    (hds : ∀ s : ℂ, 1 < s.re → Ldual s=normDirichletSeries χdual idealExponentNorm s)
    (hds2 : ∀ s : ℂ, 1 < s.re → L2dual s=normDirichletSeries χ2dual idealExponentNorm s)
    {A A2 k k2 u T : ℝ} {ε ε2 : ℂ}
    (hA : 0 < A) (hA2 : 0 < A2) (hk : 0 ≤ k) (hk2 : 0 ≤ k2)
    (hε : ‖ε‖ ≤ 1) (hε2 : ‖ε2‖ ≤ 1) (hu : 10 ≤ u)
    (huA : A ≤ u) (huA2 : A2 ≤ u) (huk : k+7 ≤ u) (huk2 : k2+7 ≤ u)
    (huT : 4+2*(T+3) ≤ u)
    (hFE : HeckeFunctionalEquation A k ε L Ldual)
    (hFE2 : HeckeFunctionalEquation A2 k2 ε2 L2 L2dual)
    (hcomp : ShiftedCompletedHeckeFiniteOrder A k L)
    (hcomp2 : ShiftedCompletedHeckeFiniteOrder A2 k2 L2)
    {σ t : ℝ} (hσ : 1-heckeZeroFreeWidth u/2 ≤ σ) (hσ2 : σ ≤ 2) (ht : |t| ≤ T) :
    ‖logDeriv L ((σ:ℂ)+(t:ℂ)*Complex.I)‖ ≤
      heckeLogSquaredConstant*(1+Real.log u)^2 := by
  sorry

end CubicFirstMoment

end

end OAI
end
