-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_QLDet_adjugate_isInt
-- name    : GlobalTheory.CompanionTheory.QLDet.adjugate_isInt
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T11:55:53.147901+00:00
-- url     : https://prove2.me/theorems/1b7cdb18-763f-485c-ac49-6e96eacd234a
-- title:
--   QLDet: adjugate is Int
-- statement:
--   The QLDet construction uses the adjugate is Int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/MemIntegralGLIffIntegralUnitDet.lean#L19-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/MemIntegralGLIffIntegralUnitDet.lean#L19-L27

import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_InstBorelGL
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_LocalFieldUniformizerNormPropertiesStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_MemIntegralGLIffIntegralUnitDet
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.QLDet
variable {F : Type} [Field F]

theorem GlobalTheory.CompanionTheory.QLDet.adjugate_isInt (O : Subring F) {n : ℕ} {M : Matrix (Fin n) (Fin n) F} (h : IsInt O M) :
    IsInt O M.adjugate := by sorry
