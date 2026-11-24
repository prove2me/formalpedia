-- Prove2me | Theorems.Thm_GlobalTheory_JR_Et_CharpolySep_squarefree_minpoly
-- name    : GlobalTheory.JR.Et.CharpolySep.squarefree_minpoly
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T17:27:05.974426+00:00
-- url     : https://prove2.me/theorems/af8502a8-7472-438a-ba63-5a893f857e36
-- title:
--   Charpoly Sep: squarefree minpoly
-- statement:
--   The Charpoly Sep construction uses the squarefree minpoly property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CharpolyEtaleGeneratorMulMatrixSeparable.lean#L8-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CharpolyEtaleGeneratorMulMatrixSeparable.lean#L8-L24

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

theorem GlobalTheory.JR.Et.CharpolySep.squarefree_minpoly {F K : Type} [Field F] [CommRing K] [Algebra F K] [IsReduced K] [Module.Finite F K]
    (τ : K) : Squarefree (minpoly F τ) := by sorry
