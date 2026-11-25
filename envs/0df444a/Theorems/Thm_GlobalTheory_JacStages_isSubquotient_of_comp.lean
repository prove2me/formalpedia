-- Prove2me | Theorems.Thm_GlobalTheory_JacStages_isSubquotient_of_comp
-- name    : GlobalTheory.JacStages.isSubquotient_of_comp
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:11:45.291271+00:00
-- url     : https://prove2.me/theorems/b4653fec-f084-4f6b-abd5-78a2aba522ff
-- title:
--   Jac Stages: is Subquotient of comp
-- statement:
--   The Jac Stages construction uses the is Subquotient of comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsSubquotientOfEquiv.lean#L92-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsSubquotientOfEquiv.lean#L92-L99

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsSubquotientOfEquiv
import Theorems.Thm_GlobalTheory_SmGL_IsSmoothChar_comp

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

theorem GlobalTheory.JacStages.isSubquotient_of_comp {σ : Representation ℂ G W} {ρ : Representation ℂ G V} (ψ : G' →* G)
    (hψ : Function.Surjective ψ) (h : IsSubquotient (σ.comp ψ) (ρ.comp ψ)) : IsSubquotient σ ρ := by sorry
