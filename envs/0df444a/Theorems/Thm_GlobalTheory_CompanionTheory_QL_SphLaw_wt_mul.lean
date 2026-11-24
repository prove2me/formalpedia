-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_QL_SphLaw_wt_mul
-- name    : GlobalTheory.CompanionTheory.QL.SphLaw.wt_mul
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T11:55:43.822559+00:00
-- url     : https://prove2.me/theorems/31d39735-82c8-44df-bdf7-5f49fb35c183
-- title:
--   Sph Law: wt mul
-- statement:
--   The Sph Law construction uses the wt mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/SphericalFunctionInvarianceProperties.lean#L46-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/SphericalFunctionInvarianceProperties.lean#L46-L62

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

theorem GlobalTheory.CompanionTheory.QL.SphLaw.wt_mul {F : Type} [Field F] {nrm : AbsoluteValue F ℝ} {q : ℕ} (hq : 1 < q)
    (hv : ∀ x : F, x ≠ 0 → ∃ e : ℤ, nrm x = (q : ℝ) ^ (-e))
    {c : ℕ} {χ : Fin c → F → ℂ} {α : Fin c → ℂ} (hU : UnrChar nrm q χ α)
    (a b : GL (Fin c) F) (ha : (a : Matrix (Fin c) (Fin c) F).BlockTriangular id)
    (hb : (b : Matrix (Fin c) (Fin c) F).BlockTriangular id) :
    wt nrm χ ((a * b : GL (Fin c) F) : Matrix (Fin c) (Fin c) F) =
      wt nrm χ (a : Matrix (Fin c) (Fin c) F) * wt nrm χ (b : Matrix (Fin c) (Fin c) F) := by sorry
