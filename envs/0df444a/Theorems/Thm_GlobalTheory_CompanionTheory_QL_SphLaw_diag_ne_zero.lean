-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_QL_SphLaw_diag_ne_zero
-- name    : GlobalTheory.CompanionTheory.QL.SphLaw.diag_ne_zero
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T11:56:04.137809+00:00
-- url     : https://prove2.me/theorems/e9244ce8-887b-446d-b17b-da460dce24f5
-- title:
--   Sph Law: diag ne zero
-- statement:
--   The Sph Law construction uses the diag ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/SphericalFunctionInvarianceProperties.lean#L22-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/SphericalFunctionInvarianceProperties.lean#L22-L27

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_InstBorelGL
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_LocalFieldUniformizerNormPropertiesStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_GeneralLinearIntegralCompactOpenStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_IwasawaDecompositionUpperTriangularStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_SphericalFunctionInvarianceProperties
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.QL GlobalTheory.CompanionTheory.QL.SphLaw

theorem GlobalTheory.CompanionTheory.QL.SphLaw.diag_ne_zero {F : Type} [Field F] {c : ℕ} (b : GL (Fin c) F)
    (hb : (b : Matrix (Fin c) (Fin c) F).BlockTriangular id) (i : Fin c) :
    (b : Matrix (Fin c) (Fin c) F) i i ≠ 0 := by sorry
