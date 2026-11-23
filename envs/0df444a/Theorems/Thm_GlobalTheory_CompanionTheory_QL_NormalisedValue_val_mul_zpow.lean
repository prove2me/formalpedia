-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_QL_NormalisedValue_val_mul_zpow
-- name    : GlobalTheory.CompanionTheory.QL.NormalisedValue.val_mul_zpow
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T20:07:26.529296+00:00
-- url     : https://prove2.me/theorems/fe133af9-b276-4460-a820-d5c738daebef
-- title:
--   Normalised Value: val mul zpow
-- statement:
--   The Normalised Value construction uses the val mul zpow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/LocalFieldUniformizerNormProperties.lean#L91-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/LocalFieldUniformizerNormProperties.lean#L91-L95

import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_InstBorelGL
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_LocalFieldUniformizerNormProperties
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix GlobalTheory.CompanionTheory.QL
open scoped ComplexConjugate ValuativeRel
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.QL GlobalTheory.CompanionTheory.QL.NormalisedValue
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {O : Subring F} {ϖ : F} {nrm : AbsoluteValue F ℝ} {q : ℕ}

theorem GlobalTheory.CompanionTheory.QL.NormalisedValue.val_mul_zpow (h : LF O ϖ nrm q) {x : F} {e : ℤ}
    (he : ValuativeRel.valuation F x = ValuativeRel.valuation F ϖ ^ e) :
    ValuativeRel.valuation F (x * ϖ ^ (-e)) = 1 := by sorry
