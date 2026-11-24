-- Prove2me | Theorems.Thm_GlobalTheory_JR_Et_CharpolySep_charpoly_lmul_eq_minpoly
-- name    : GlobalTheory.JR.Et.CharpolySep.charpoly_lmul_eq_minpoly
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T17:27:13.36472+00:00
-- url     : https://prove2.me/theorems/b1408ca0-179e-4f3c-90ab-479cbbed8435
-- title:
--   Charpoly Sep: charpoly lmul eq minpoly
-- statement:
--   The Charpoly Sep construction uses the charpoly lmul eq minpoly property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CharpolyEtaleGeneratorMulMatrixSeparable.lean#L26-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CharpolyEtaleGeneratorMulMatrixSeparable.lean#L26-L51

import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MulMatMemUnitaryGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CharpolyEtaleGeneratorMulMatrixSeparable
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
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.Et GlobalTheory.JR.Et.CharpolySep

theorem GlobalTheory.JR.Et.CharpolySep.charpoly_lmul_eq_minpoly {F K : Type} [Field F] [CommRing K] [Algebra F K] [Module.Finite F K] {r : ℕ}
    (τ : K) (hli : LinearIndependent F (fun i : Fin r => τ ^ (i : ℕ))) (hr : Module.finrank F K = r) :
    (Algebra.lmul F K τ).charpoly = minpoly F τ := by sorry
