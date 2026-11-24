-- Prove2me | Theorems.Thm_GlobalTheory_WeilSmooth_mid_eq
-- name    : GlobalTheory.WeilSmooth.mid_eq
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T21:55:24.925173+00:00
-- url     : https://prove2.me/theorems/383af488-f82c-44ad-8e37-4f7c546fc933
-- title:
--   Weil Smooth: mid eq
-- statement:
--   The Weil Smooth construction uses the mid eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/WeilRepEvalZeroMemInduced.lean#L23-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/WeilRepEvalZeroMemInduced.lean#L23-L32

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

theorem GlobalTheory.WeilSmooth.mid_eq {k : Type} [CommRing k] (a a' t t' : k) (ha : a * a' = 1) (ht : t * t' = 1) :
    ((nS ((a - 1) * t') * lS t * nS ((a' - 1) * t') * lS (-(t * a)) : SpecialLinearGroup (Fin 2) k) :
      Matrix (Fin 2) (Fin 2) k) = !![a, 0; 0, a'] := by sorry
