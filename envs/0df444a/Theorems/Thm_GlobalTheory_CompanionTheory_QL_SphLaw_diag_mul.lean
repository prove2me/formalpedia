-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_QL_SphLaw_diag_mul
-- name    : GlobalTheory.CompanionTheory.QL.SphLaw.diag_mul
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T11:55:53.931964+00:00
-- url     : https://prove2.me/theorems/912924fb-185c-49f6-958a-4bb014f88be8
-- title:
--   Sph Law: diag mul
-- statement:
--   The Sph Law construction uses the diag mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/SphericalFunctionInvarianceProperties.lean#L12-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/SphericalFunctionInvarianceProperties.lean#L12-L20

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

theorem GlobalTheory.CompanionTheory.QL.SphLaw.diag_mul {F : Type} [Field F] {c : ℕ} {a b : Matrix (Fin c) (Fin c) F}
    (ha : a.BlockTriangular id) (hb : b.BlockTriangular id) (i : Fin c) :
    (a * b) i i = a i i * b i i := by sorry
