-- Prove2me | Theorems.Thm_GlobalTheory_JacStages_flatHom_apply
-- name    : GlobalTheory.JacStages.flatHom_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:33:06.581803+00:00
-- url     : https://prove2.me/theorems/be1eafe1-cfc8-4d1e-ad9d-0121bd0110cd
-- title:
--   Jac Stages: flat Hom apply
-- statement:
--   The Jac Stages construction uses the flat Hom apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsSubquotientOfEquiv.lean#L75-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsSubquotientOfEquiv.lean#L75-L77

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
variable {s : ℕ} {t : Fin s → ℕ}

theorem GlobalTheory.JacStages.flatHom_apply (Γ : ∀ a, Fin (t a) → Type) [∀ a b, Group (Γ a b)] (g : ∀ a b, Γ a b)
    (c : Fin (∑ a, t a)) :
    flatHom Γ g c = g (finSigmaFinEquiv.symm c).1 (finSigmaFinEquiv.symm c).2 := by sorry
