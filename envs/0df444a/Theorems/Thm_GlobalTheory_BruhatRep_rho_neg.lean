-- Prove2me | Theorems.Thm_GlobalTheory_BruhatRep_rho_neg
-- name    : GlobalTheory.BruhatRep.rho_neg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:01:23.110795+00:00
-- url     : https://prove2.me/theorems/c57f70dc-a51d-4093-88a2-0c8fa692bd62
-- title:
--   Bruhat Rep: rho neg
-- statement:
--   The Bruhat Rep construction uses the rho neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/Sl2PresentationRelations.lean#L125-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/Sl2PresentationRelations.lean#L125-L127

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
variable (n : K → M) (m : Kˣ → M) (t : M)

theorem GlobalTheory.BruhatRep.rho_neg {g : SpecialLinearGroup (Fin 2) K} (h : en g 1 0 ≠ 0) :
    rho n m t g = n (en g 0 0 / en g 1 0) * mx m (-1 / en g 1 0) * t * n (en g 1 1 / en g 1 0) := by sorry
