-- Prove2me | Theorems.Thm_GlobalTheory_FinEt_exists_section_of_isSepClosed
-- name    : GlobalTheory.FinEt.exists_section_of_isSepClosed
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T13:24:11.782802+00:00
-- url     : https://prove2.me/theorems/8e558342-9936-49fb-a11c-7f0a88560dfe
-- title:
--   Fin Et: exists section of is Sep Closed
-- statement:
--   The Fin Et construction uses the exists section of is Sep Closed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsIsoIffBijectiveOverAlgClosed.lean#L612-L631
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsIsoIffBijectiveOverAlgClosed.lean#L612-L631

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoIffBijectiveOverAlgClosed
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits TopologicalSpace AlgebraicGeometry
universe u
noncomputable section
open GlobalTheory GlobalTheory.FinEt
attribute [local simp] pullback.lift_fst pullback.lift_snd pullback.lift_fst_assoc
  pullback.lift_snd_assoc
variable {S : Scheme.{u}} {X Y : Over S}

theorem GlobalTheory.FinEt.exists_section_of_isSepClosed {k : Type u} [Field k] [IsSepClosed k] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of k)) [IsFinite p] [Etale p] [Nonempty X] :
    ∃ σ : Spec (.of k) ⟶ X, σ ≫ p = 𝟙 _ := by sorry
