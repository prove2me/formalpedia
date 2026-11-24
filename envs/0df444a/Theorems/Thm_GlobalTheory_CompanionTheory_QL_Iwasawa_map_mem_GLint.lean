-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_QL_Iwasawa_map_mem_GLint
-- name    : GlobalTheory.CompanionTheory.QL.Iwasawa.map_mem_GLint
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T11:56:33.181771+00:00
-- url     : https://prove2.me/theorems/9937659b-9b1c-40f1-aa7d-de3d3616929f
-- title:
--   Iwasawa: map mem GLint
-- statement:
--   The Iwasawa construction uses the map mem GLint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/IwasawaDecompositionUpperTriangular.lean#L8-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/IwasawaDecompositionUpperTriangular.lean#L8-L21

import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_InstBorelGL
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsOfValILeOne
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_IwasawaDecompositionUpperTriangular
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.QL GlobalTheory.CompanionTheory.QL.Iwasawa

theorem GlobalTheory.CompanionTheory.QL.Iwasawa.map_mem_GLint {F : Type} [Field F] [ValuativeRel F] {n : ℕ}
    (k : GL (Fin n) (ValuativeRel.valuation F).valuationSubring) :
    GeneralLinearGroup.map (algebraMap (ValuativeRel.valuation F).valuationSubring F) k ∈
      GLint 𝒪[F] n := by sorry
