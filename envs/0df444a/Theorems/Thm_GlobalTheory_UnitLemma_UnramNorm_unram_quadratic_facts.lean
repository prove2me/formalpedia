-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_UnramNorm_unram_quadratic_facts
-- name    : GlobalTheory.UnitLemma.UnramNorm.unram_quadratic_facts
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:32:40.414631+00:00
-- url     : https://prove2.me/theorems/e42370a4-a338-434f-9af1-53504c45e7ef
-- title:
--   Unram Norm: unram quadratic facts
-- statement:
--   The Unram Norm construction uses the unram quadratic facts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnramifiedQuadraticNormsTraceUniformizerFacts.lean#L179-L305
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnramifiedQuadraticNormsTraceUniformizerFacts.lean#L179-L305

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

theorem GlobalTheory.UnitLemma.UnramNorm.unram_quadratic_facts :
    ∀ (K : _root_.GlobalTheory.UnitLemma.UQ), (∀ u : K.Oˣ, K.c (algebraMap K.O K.E u) = algebraMap K.O K.E u →
    ∃ z : K.Oˣ, algebraMap K.O K.E u = algebraMap K.O K.E z * K.c (algebraMap K.O K.E z)) ∧
    (∃ z : K.O, algebraMap K.O K.E z + K.c (algebraMap K.O K.E z) = 1) ∧
    (∃ ϖ : K.O, Irreducible ϖ ∧ K.c (algebraMap K.O K.E ϖ) = algebraMap K.O K.E ϖ) ∧
    ∀ x : K.E, _root_.GlobalTheory.UnitLemma.val K.O (K.c x) = _root_.GlobalTheory.UnitLemma.val K.O x := by sorry
