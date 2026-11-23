-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_UnramNorm_cO_spec
-- name    : GlobalTheory.UnitLemma.UnramNorm.cO_spec
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:10:25.322834+00:00
-- url     : https://prove2.me/theorems/2441efb6-4dba-4f9c-a999-89cd0802c407
-- title:
--   Unram Norm: c O spec
-- statement:
--   The Unram Norm construction uses the c O spec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnramifiedQuadraticNormsTraceUniformizerFacts.lean#L36-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnramifiedQuadraticNormsTraceUniformizerFacts.lean#L36-L38

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

theorem GlobalTheory.UnitLemma.UnramNorm.cO_spec (x : K.O) :
    algebraMap K.O K.E (_root_.GlobalTheory.UnitLemma.UnramNorm.cO K x) = K.c (algebraMap K.O K.E x) := by sorry
