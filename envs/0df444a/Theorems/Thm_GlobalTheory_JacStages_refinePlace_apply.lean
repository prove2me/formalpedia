-- Prove2me | Theorems.Thm_GlobalTheory_JacStages_refinePlace_apply
-- name    : GlobalTheory.JacStages.refinePlace_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:33:09.803824+00:00
-- url     : https://prove2.me/theorems/8f260ac2-1627-458b-92ec-12608a40f967
-- title:
--   Jac Stages: refine Place apply
-- statement:
--   The Jac Stages construction uses the refine Place apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsSubquotientOfEquiv.lean#L63-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsSubquotientOfEquiv.lean#L63-L67

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

theorem GlobalTheory.JacStages.refinePlace_apply {n : ℕ} {d : Fin s → ℕ} (e : (Σ a, Fin (d a)) ≃ Fin n) {d' : ∀ a, Fin (t a) → ℕ}
    (e' : ∀ a, (Σ b, Fin (d' a b)) ≃ Fin (d a)) (c : Fin (∑ a, t a))
    (i : Fin (d' (finSigmaFinEquiv.symm c).1 (finSigmaFinEquiv.symm c).2)) :
    refinePlace e e' ⟨c, i⟩ =
      e ⟨(finSigmaFinEquiv.symm c).1, e' _ ⟨(finSigmaFinEquiv.symm c).2, i⟩⟩ := by sorry
