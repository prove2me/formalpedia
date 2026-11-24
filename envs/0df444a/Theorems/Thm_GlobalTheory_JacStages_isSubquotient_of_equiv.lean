-- Prove2me | Theorems.Thm_GlobalTheory_JacStages_isSubquotient_of_equiv
-- name    : GlobalTheory.JacStages.isSubquotient_of_equiv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:34:06.402219+00:00
-- url     : https://prove2.me/theorems/3cb65863-8db6-44dd-8b48-7abf18691bb7
-- title:
--   Jac Stages: is Subquotient of equiv
-- statement:
--   The Jac Stages construction uses the is Subquotient of equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsSubquotientOfEquiv.lean#L101-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsSubquotientOfEquiv.lean#L101-L103

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsSubquotientOfEquiv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SmGL
open GlobalTheory GlobalTheory.JacStages
variable {G G' V W : Type} [Group G] [Group G'] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem GlobalTheory.JacStages.isSubquotient_of_equiv {σ : Representation ℂ G W} {ρ : Representation ℂ G V} (φ : σ.Equiv ρ) :
    IsSubquotient σ ρ := by sorry
