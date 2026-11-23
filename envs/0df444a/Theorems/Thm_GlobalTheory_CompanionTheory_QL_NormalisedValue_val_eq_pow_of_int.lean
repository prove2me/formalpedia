-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_QL_NormalisedValue_val_eq_pow_of_int
-- name    : GlobalTheory.CompanionTheory.QL.NormalisedValue.val_eq_pow_of_int
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:07:07.425569+00:00
-- url     : https://prove2.me/theorems/71c72ed1-d6e3-41ff-a593-f1e2ec059efc
-- title:
--   Normalised Value: val eq pow of int
-- statement:
--   The Normalised Value construction uses the val eq pow of int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/LocalFieldUniformizerNormProperties.lean#L66-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/LocalFieldUniformizerNormProperties.lean#L66-L78

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

theorem GlobalTheory.CompanionTheory.QL.NormalisedValue.val_eq_pow_of_int (h : LF O ϖ nrm q) {x : F} (hx : x ≠ 0)
    (hxO : ValuativeRel.valuation F x ≤ 1) :
    ∃ n : ℕ, ValuativeRel.valuation F x = ValuativeRel.valuation F ϖ ^ n := by sorry
