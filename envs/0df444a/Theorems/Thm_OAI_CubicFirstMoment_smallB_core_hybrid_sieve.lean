-- Prove2me | Theorems.Thm_OAI_CubicFirstMoment_smallB_core_hybrid_sieve
-- name    : OAI.CubicFirstMoment.smallB_core_hybrid_sieve
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-30T04:03:36.240691+00:00
-- url     : https://prove2.me/theorems/a482a8a1-b990-41bd-95ea-09e3bb22cff2
-- title:
--   OAI.CubicFirstMoment.smallB_core_hybrid_sieve: intermediate lemma from OpenAI, An unconditional first moment for cubic Gauss sums (result family 023)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CubicFirstMoment.patterson_firstMoment`, `OAI.CubicFirstMoment.patterson_angularComparison` and `OAI.CubicFirstMoment.patterson_angularCancellation`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An unconditional first moment for cubic Gauss sums (result family 023)*, OpenAI Math Release, September 25, 2026, result family 23, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CubicFirstMoment.smallB_core_hybrid_sieve` of [lean/OAI/NumberTheory/CubicMoment/Estimates/SmallBCoreHybrid.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/CubicMoment/Estimates/SmallBCoreHybrid.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CubicFirstMoment`, with `open scoped BigOperators`):
--
--   ```lean
--   theorem smallB_core_hybrid_sieve (hHuxley : HuxleyAdditiveLargeSieve) :
--       ∃ K : ℝ, 0 < K ∧ ∀ (S H : Finset Eisenstein) (β : Eisenstein → ℂ)
--         (N B V : ℝ) (i j : ℕ), 65536 ≤ N → 0 ≤ B → 0 < V →
--         (∀ b ∈ S, primary b ∧ Squarefree b ∧ norm b ≤ N) →
--         V/5832 ≤ coreDyadicConductor i j → 8*coreDyadicConductor i j ≤ N^(3/4:ℝ) →
--         H ⊆ coreDyadicBlock B i j →
--         (∑ h ∈ H, ‖∑ b ∈ S, β b*cubicSymbol b h‖^2) ≤
--           K*B^(1/3:ℝ)*(N*(V/5832)^(-(1/4:ℝ))+N^(1-1/20000:ℝ))*
--             ∑ b ∈ S, ‖β b‖^2
--   ```
--
--   **Definitions.** The statement is written with `OAI.CubicFirstMoment.cubicSymbol` (definitions bundle `OAIQ096A000` of this split); `OAI.CubicFirstMoment.coreDyadicConductor` (definitions bundle `OAIQ096A002` of this split); `OAI.CubicFirstMoment.HuxleyAdditiveLargeSieve` (definitions bundle `OAIQ096A007` of this split); `OAI.CubicFirstMoment.coreDyadicBlock` (definitions bundle `OAIQ096A008` of this split); `OAI.CubicFirstMoment.Eisenstein`, `OAI.CubicFirstMoment.norm` and `OAI.CubicFirstMoment.primary` (the published bundle `Def_PattersonFirstMoment`).
--
--   **Used by.** The proofs of `OAI_CubicFirstMoment_ProfileControl_low_coprime_mellin_height_log_saving`, `OAI.CubicFirstMoment.ProfileControl.low_poisson_dyadic_height_log_saving`, `OAI.CubicFirstMoment.angular_stopped_early_divisor_noncube_mass`, `OAI_CubicFirstMoment_angular_stopped_noncube_core_blocks`, `OAI.CubicFirstMoment.angular_stopped_noncube_mass`, `OAI.CubicFirstMoment.angular_stopped_noncube_radial_form`, `OAI_CubicFirstMoment_angular_stopped_rough_divisor_log`, `OAI_CubicFirstMoment_bounded_divisor_arithmetic_mellin_tail`, `OAI.CubicFirstMoment.bounded_poisson_dyadic`, `OAI.CubicFirstMoment.stopped_early_divisor_noncube_mass`, `OAI_CubicFirstMoment_stopped_noncube_mass`, `OAI.CubicFirstMoment.stopped_noncube_radial_form` and `OAI_CubicFirstMoment_stopped_rough_divisor_log` of this split import it.
-- source:
--   OpenAI, An unconditional first moment for cubic Gauss sums (result family 023), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 23; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-unconditional-first-moment-for-cubic-Gauss-sums-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/CubicMoment/Estimates/SmallBCoreHybrid.lean (declaration OAI.CubicFirstMoment.smallB_core_hybrid_sieve)

import Mathlib
import Definitions.Def_PattersonFirstMoment
import Definitions.Def_OAIQ096A007
import Definitions.Def_OAIQ096A008

section

attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

theorem smallB_core_hybrid_sieve (hHuxley : HuxleyAdditiveLargeSieve) :
    ∃ K : ℝ, 0 < K ∧ ∀ (S H : Finset Eisenstein) (β : Eisenstein → ℂ)
      (N B V : ℝ) (i j : ℕ), 65536 ≤ N → 0 ≤ B → 0 < V →
      (∀ b ∈ S, primary b ∧ Squarefree b ∧ norm b ≤ N) →
      V/5832 ≤ coreDyadicConductor i j → 8*coreDyadicConductor i j ≤ N^(3/4:ℝ) →
      H ⊆ coreDyadicBlock B i j →
      (∑ h ∈ H, ‖∑ b ∈ S, β b*cubicSymbol b h‖^2) ≤
        K*B^(1/3:ℝ)*(N*(V/5832)^(-(1/4:ℝ))+N^(1-1/20000:ℝ))*
          ∑ b ∈ S, ‖β b‖^2 := by
  sorry

end CubicFirstMoment

end

end OAI
end
