-- Prove2me | Theorems.Thm_OAI_CubicFirstMoment_dilated_noncube_three_sieve_bounds
-- name    : OAI.CubicFirstMoment.dilated_noncube_three_sieve_bounds
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T03:58:46.301984+00:00
-- url     : https://prove2.me/theorems/548a8480-ff59-47b8-a4c4-4390886ce764
-- title:
--   OAI.CubicFirstMoment.dilated_noncube_three_sieve_bounds: intermediate lemma from OpenAI, An unconditional first moment for cubic Gauss sums (result family 023)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CubicFirstMoment.patterson_firstMoment`, `OAI.CubicFirstMoment.patterson_angularComparison` and `OAI.CubicFirstMoment.patterson_angularCancellation`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An unconditional first moment for cubic Gauss sums (result family 023)*, OpenAI Math Release, September 25, 2026, result family 23, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CubicFirstMoment.dilated_noncube_three_sieve_bounds` of [lean/OAI/NumberTheory/CubicMoment/Estimates/DilatedNoncubeSieve.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/CubicMoment/Estimates/DilatedNoncubeSieve.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CubicFirstMoment`, with `open scoped BigOperators`):
--
--   ```lean
--   theorem dilated_noncube_three_sieve_bounds (hHuxley : HuxleyAdditiveLargeSieve)
--       {K ε : ℝ} (hK : 1 ≤ K) (hε : 0 < ε) :
--       ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧
--       ∀ (B R S T J H : Finset Eisenstein) (N U V : ℝ),
--         1 ≤ N → 1 ≤ U → 1 ≤ V →
--         (∀ b ∈ B, primary b ∧ Squarefree b ∧ norm b ≤ K*N) →
--         (∀ s ∈ S, primary s ∧ Squarefree s ∧ norm s ≤ U) →
--         (∀ t ∈ T, primary t ∧ Squarefree t ∧ norm t ≤ V) →
--         H ⊆ coprimeResidualSupport R J (coprimePairs S T) →
--         ∀ β : Eisenstein → ℂ,
--         (∑ h ∈ H, ‖∑ b ∈ B, β b*cubicSymbol b h‖^2) ≤
--           min ((R.card:ℝ)*J.card*C₁ *
--             min ((T.card:ℝ)*(U*N)^ε*(U+N+(U*N)^(2/3:ℝ)))
--                 ((S.card:ℝ)*(V*N)^ε*(V+N+(V*N)^(2/3:ℝ))))
--             ((R.card:ℝ)*J.card*C₂*(U*V)^ε*((U*V)^2+N)) *
--               ∑ b ∈ B, ‖β b‖^2
--   ```
--
--   **Definitions.** The statement is written with `OAI.CubicFirstMoment.cubicSymbol` (definitions bundle `OAIQ096A000` of this split); `OAI.CubicFirstMoment.HuxleyAdditiveLargeSieve` (definitions bundle `OAIQ096A007` of this split); `OAI.CubicFirstMoment.coprimePairs` and `OAI.CubicFirstMoment.coprimeResidualSupport` (definitions bundle `OAIQ096A008` of this split); `OAI.CubicFirstMoment.Eisenstein`, `OAI.CubicFirstMoment.norm` and `OAI.CubicFirstMoment.primary` (the published bundle `Def_PattersonFirstMoment`).
--
--   **Used by.** The proofs of `OAI_CubicFirstMoment_angular_height_all_frequency_cutoff_mass`, `OAI.CubicFirstMoment.angular_height_signed_mellin_saving`, `OAI_CubicFirstMoment_angular_large_core_block_moment`, `OAI.CubicFirstMoment.angular_large_core_mellin_integral_saving` and `OAI.CubicFirstMoment.uniform_core_block_polynomial_height` of this split import it.
-- source:
--   OpenAI, An unconditional first moment for cubic Gauss sums (result family 023), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 23; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-unconditional-first-moment-for-cubic-Gauss-sums-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/CubicMoment/Estimates/DilatedNoncubeSieve.lean (declaration OAI.CubicFirstMoment.dilated_noncube_three_sieve_bounds)

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

theorem dilated_noncube_three_sieve_bounds (hHuxley : HuxleyAdditiveLargeSieve)
    {K ε : ℝ} (hK : 1 ≤ K) (hε : 0 < ε) :
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧
    ∀ (B R S T J H : Finset Eisenstein) (N U V : ℝ),
      1 ≤ N → 1 ≤ U → 1 ≤ V →
      (∀ b ∈ B, primary b ∧ Squarefree b ∧ norm b ≤ K*N) →
      (∀ s ∈ S, primary s ∧ Squarefree s ∧ norm s ≤ U) →
      (∀ t ∈ T, primary t ∧ Squarefree t ∧ norm t ≤ V) →
      H ⊆ coprimeResidualSupport R J (coprimePairs S T) →
      ∀ β : Eisenstein → ℂ,
      (∑ h ∈ H, ‖∑ b ∈ B, β b*cubicSymbol b h‖^2) ≤
        min ((R.card:ℝ)*J.card*C₁ *
          min ((T.card:ℝ)*(U*N)^ε*(U+N+(U*N)^(2/3:ℝ)))
              ((S.card:ℝ)*(V*N)^ε*(V+N+(V*N)^(2/3:ℝ))))
          ((R.card:ℝ)*J.card*C₂*(U*V)^ε*((U*V)^2+N)) *
            ∑ b ∈ B, ‖β b‖^2 := by
  sorry

end CubicFirstMoment

end

end OAI
end
