-- Prove2me | Theorems.Thm_GlobalTheory_BruhatRep_a_ne
-- name    : GlobalTheory.BruhatRep.a_ne
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:02:04.817538+00:00
-- url     : https://prove2.me/theorems/cc4ee5b1-d326-43f1-9823-509e183b99d8
-- title:
--   Bruhat Rep: a ne
-- statement:
--   The Bruhat Rep construction uses the a ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/Sl2PresentationRelations.lean#L48-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/Sl2PresentationRelations.lean#L48-L49

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
variable {M : Type} [Monoid M]

theorem GlobalTheory.BruhatRep.a_ne (g : SpecialLinearGroup (Fin 2) K) (hc : en g 1 0 = 0) : en g 0 0 ≠ 0 := by sorry
