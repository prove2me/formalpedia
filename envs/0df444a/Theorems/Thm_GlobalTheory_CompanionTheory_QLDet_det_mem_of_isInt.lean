-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_QLDet_det_mem_of_isInt
-- name    : GlobalTheory.CompanionTheory.QLDet.det_mem_of_isInt
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T11:56:01.88763+00:00
-- url     : https://prove2.me/theorems/d521668a-e593-4737-846b-1e06c13bdb72
-- title:
--   QLDet: det mem of is Int
-- statement:
--   The QLDet construction uses the det mem of is Int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/MemIntegralGLIffIntegralUnitDet.lean#L10-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/MemIntegralGLIffIntegralUnitDet.lean#L10-L17

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

theorem GlobalTheory.CompanionTheory.QLDet.det_mem_of_isInt (O : Subring F) {n : ℕ} {M : Matrix (Fin n) (Fin n) F} (h : IsInt O M) :
    M.det ∈ O := by sorry
