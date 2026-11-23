-- Prove2me | Theorems.Thm_GlobalTheory_BruhatRep_en_mul
-- name    : GlobalTheory.BruhatRep.en_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:02:08.193799+00:00
-- url     : https://prove2.me/theorems/7be8b030-3377-49e2-8ef2-f48d0c8ead10
-- title:
--   Bruhat Rep: en mul
-- statement:
--   The Bruhat Rep construction uses the en mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/Sl2PresentationRelations.lean#L17-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/Sl2PresentationRelations.lean#L17-L19

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsStableGauss
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_Sl2PresentationRelations
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.BruhatRep
variable {K : Type} [Field K]

theorem GlobalTheory.BruhatRep.en_mul (g h : SpecialLinearGroup (Fin 2) K) (i j : Fin 2) :
    en (g * h) i j = en g i 0 * en h 0 j + en g i 1 * en h 1 j := by sorry
