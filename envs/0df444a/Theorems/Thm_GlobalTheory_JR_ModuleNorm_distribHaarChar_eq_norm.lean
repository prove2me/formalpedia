-- Prove2me | Theorems.Thm_GlobalTheory_JR_ModuleNorm_distribHaarChar_eq_norm
-- name    : GlobalTheory.JR.ModuleNorm.distribHaarChar_eq_norm
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T20:37:47.221814+00:00
-- url     : https://prove2.me/theorems/afa460b2-8e98-46b1-9bef-ee85e7e6014a
-- title:
--   Module Norm: distrib Haar Char eq norm
-- statement:
--   The Module Norm construction uses the distrib Haar Char eq norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/DistribHaarCharTransport.lean#L53-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/DistribHaarCharTransport.lean#L53-L81

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DistribHaarCharTransport
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR MeasureTheory Filter Topology
open scoped Pointwise
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.ModuleNorm

theorem GlobalTheory.JR.ModuleNorm.distribHaarChar_eq_norm (K L : Type) [CommRing K] [TopologicalSpace K]
    [IsTopologicalRing K] [T2Space K] [LocallyCompactSpace K] [SecondCountableTopology K]
    [CommRing L] [TopologicalSpace L] [IsTopologicalRing L] [T2Space L] [LocallyCompactSpace L]
    [SecondCountableTopology L] [StarRing L] [ContinuousStar L] [Algebra K L]
    (e : (Fin 2 → K) ≃ₗ[K] L) (he : Continuous e) (hes : Continuous e.symm) (y : Lˣ) (k : Kˣ)
    (h : algebraMap K L k = y * star (y : L)) :
    distribHaarChar L y = distribHaarChar K k := by sorry
