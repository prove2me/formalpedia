-- Prove2me | Theorems.Thm_GlobalTheory_WeilSmooth_decomp
-- name    : GlobalTheory.WeilSmooth.decomp
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T21:55:42.451621+00:00
-- url     : https://prove2.me/theorems/be6a0e74-2712-4706-9ffc-c7b0b0c02d67
-- title:
--   Weil Smooth: decomp
-- statement:
--   The Weil Smooth construction uses the decomp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/WeilRepEvalZeroMemInduced.lean#L34-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/WeilRepEvalZeroMemInduced.lean#L34-L49

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ContinuousEtaleHermitianPairNormAndMapZeroStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EtaleHermitianPairEventuallyIsUnitContinuousAtInStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WeilRepEvalZeroMemInduced
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.WeilSmooth

theorem GlobalTheory.WeilSmooth.decomp {k : Type} [CommRing k] (g : SpecialLinearGroup (Fin 2) k) (a' t t' : k)
    (ha : (g : Matrix (Fin 2) (Fin 2) k) 0 0 * a' = 1) (ht : t * t' = 1) :
    g = lS ((g : Matrix (Fin 2) (Fin 2) k) 1 0 * a') * (nS (((g : Matrix (Fin 2) (Fin 2) k) 0 0 - 1) * t') * lS t *
      nS ((a' - 1) * t') * lS (-(t * (g : Matrix (Fin 2) (Fin 2) k) 0 0))) *
      nS ((g : Matrix (Fin 2) (Fin 2) k) 0 1 * a') := by sorry
