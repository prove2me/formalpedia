-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_HInv_det_mul_conj_eq_one
-- name    : GlobalTheory.CompanionTheory.SW.HInv.det_mul_conj_eq_one
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T12:05:51.187417+00:00
-- url     : https://prove2.me/theorems/3cb183a0-a204-4863-ab85-d0da0b1265fe
-- title:
--   HInv: det mul conj eq one
-- statement:
--   The HInv construction uses the det mul conj eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/UnitaryActionPreservesHaarLocal.lean#L12-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/UnitaryActionPreservesHaarLocal.lean#L12-L20

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorInvolutionAlgebraProperties
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_MapMulVecEqSmul
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_MapMulEqOfNormOne
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRingStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_UnitaryActionPreservesHaarLocal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.HInv

theorem GlobalTheory.CompanionTheory.SW.HInv.det_mul_conj_eq_one {A : Type} [CommRing A] {m : Type} [Fintype m] [DecidableEq m]
    (τ : A →+* A) (g J : Matrix m m A) (hg : cT τ g * J * g = J) (hJ : IsUnit J.det) :
    g.det * τ g.det = 1 := by sorry
