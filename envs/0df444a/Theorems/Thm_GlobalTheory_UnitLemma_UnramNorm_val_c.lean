-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_UnramNorm_val_c
-- name    : GlobalTheory.UnitLemma.UnramNorm.val_c
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:10:34.249787+00:00
-- url     : https://prove2.me/theorems/b3026df0-996b-4f25-a757-d3097f9ae160
-- title:
--   Unram Norm: val c
-- statement:
--   The Unram Norm construction uses the val c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnramifiedQuadraticNormsTraceUniformizerFacts.lean#L89-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnramifiedQuadraticNormsTraceUniformizerFacts.lean#L89-L95

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedQuadraticNormsTraceUniformizerFacts
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.UnramNorm
open IsLocalRing Polynomial
variable (K : UQ)
open IsLocalRing Polynomial
variable (K : _root_.GlobalTheory.UnitLemma.UQ)

theorem GlobalTheory.UnitLemma.UnramNorm.val_c (x : K.E) :
    _root_.GlobalTheory.UnitLemma.val K.O (K.c x) = _root_.GlobalTheory.UnitLemma.val K.O x := by sorry
