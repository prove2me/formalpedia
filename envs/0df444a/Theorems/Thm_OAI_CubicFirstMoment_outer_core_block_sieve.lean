-- Prove2me | Theorems.Thm_OAI_CubicFirstMoment_outer_core_block_sieve
-- name    : OAI.CubicFirstMoment.outer_core_block_sieve
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-30T04:02:08.479018+00:00
-- url     : https://prove2.me/theorems/4569b63e-3026-4ff7-bfeb-16a8aeb25a8e
-- title:
--   OAI.CubicFirstMoment.outer_core_block_sieve: intermediate lemma from OpenAI, An unconditional first moment for cubic Gauss sums (result family 023)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CubicFirstMoment.patterson_firstMoment`, `OAI.CubicFirstMoment.patterson_angularComparison` and `OAI.CubicFirstMoment.patterson_angularCancellation`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An unconditional first moment for cubic Gauss sums (result family 023)*, OpenAI Math Release, September 25, 2026, result family 23, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CubicFirstMoment.outer_core_block_sieve` of [lean/OAI/NumberTheory/CubicMoment/Estimates/OuterCoreBlock.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/CubicMoment/Estimates/OuterCoreBlock.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CubicFirstMoment`, with `open scoped BigOperators`):
--
--   ```lean
--   theorem outer_core_block_sieve {ε : ℝ} (hε : 0 < ε) :
--       ∃ C : ℝ, 0 < C ∧ ∀ (S H : Finset Eisenstein) (B N : ℝ) (i j : ℕ),
--         0 ≤ B → 1 ≤ N → coreDyadicConductor i j ≤ B →
--         (∀ n ∈ S, primary n ∧ Squarefree n ∧ norm n ≤ N) →
--         H ⊆ coreDyadicBlock B i j → ∀ β : Eisenstein → ℂ,
--         (∑ h ∈ H, ‖∑ n ∈ S, β n*cubicSymbol n h‖^2) ≤
--           C*(2*B*N)^ε*(B+(B*N)^(2/3:ℝ)+B^(1/3:ℝ)*N)*
--             ∑ n ∈ S, ‖β n‖^2
--   ```
--
--   **Definitions.** The statement is written with `OAI.CubicFirstMoment.cubicSymbol` (definitions bundle `OAIQ096A000` of this split); `OAI.CubicFirstMoment.coreDyadicConductor` (definitions bundle `OAIQ096A002` of this split); `OAI.CubicFirstMoment.coreDyadicBlock` (definitions bundle `OAIQ096A008` of this split); `OAI.CubicFirstMoment.Eisenstein`, `OAI.CubicFirstMoment.norm` and `OAI.CubicFirstMoment.primary` (the published bundle `Def_PattersonFirstMoment`).
--
--   **Used by.** The proofs of `OAI.CubicFirstMoment.ProfileControl.low_variance_remainder_height_log_saving`, `OAI.CubicFirstMoment.ProfileControl.smallB_variance_remainder_height_power`, `OAI.CubicFirstMoment.angular_coprime_noncube_mellin_integral_saving`, `OAI.CubicFirstMoment.angular_height_poisson_dyadic_saving`, `OAI.CubicFirstMoment.angular_stopped_early_divisor_noncube_mass`, `OAI.CubicFirstMoment.coprime_noncube_mellin_integral_saving`, `OAI.CubicFirstMoment.fullPrime_divisor_noncoprime_outer`, `OAI.CubicFirstMoment.height_radial_form_saving`, `OAI.CubicFirstMoment.large_common_nonzero_power` and `OAI.CubicFirstMoment.stopped_early_divisor_noncube_mass` of this split import it.
-- source:
--   OpenAI, An unconditional first moment for cubic Gauss sums (result family 023), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 23; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-unconditional-first-moment-for-cubic-Gauss-sums-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/CubicMoment/Estimates/OuterCoreBlock.lean (declaration OAI.CubicFirstMoment.outer_core_block_sieve)

import Mathlib
import Definitions.Def_PattersonFirstMoment
import Definitions.Def_OAIQ096A008

section

attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

theorem outer_core_block_sieve {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S H : Finset Eisenstein) (B N : ℝ) (i j : ℕ),
      0 ≤ B → 1 ≤ N → coreDyadicConductor i j ≤ B →
      (∀ n ∈ S, primary n ∧ Squarefree n ∧ norm n ≤ N) →
      H ⊆ coreDyadicBlock B i j → ∀ β : Eisenstein → ℂ,
      (∑ h ∈ H, ‖∑ n ∈ S, β n*cubicSymbol n h‖^2) ≤
        C*(2*B*N)^ε*(B+(B*N)^(2/3:ℝ)+B^(1/3:ℝ)*N)*
          ∑ n ∈ S, ‖β n‖^2 := by
  sorry

end CubicFirstMoment

end

end OAI
end
