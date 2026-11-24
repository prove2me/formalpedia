-- Prove2me | Theorems.Thm_GlobalTheory_FinEt_exists_iso_sigma_of_isSepClosed
-- name    : GlobalTheory.FinEt.exists_iso_sigma_of_isSepClosed
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T13:23:59.874255+00:00
-- url     : https://prove2.me/theorems/4d21b34a-a3c0-4b59-bd46-f668f91e38a9
-- title:
--   Fin Et: exists iso sigma of is Sep Closed
-- statement:
--   The Fin Et construction uses the exists iso sigma of is Sep Closed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsIsoIffBijectiveOverAlgClosed.lean#L644-L649
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsIsoIffBijectiveOverAlgClosed.lean#L644-L649

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

theorem GlobalTheory.FinEt.exists_iso_sigma_of_isSepClosed {k : Type u} [Field k] [IsSepClosed k] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of k)) [IsFinite p] [Etale p] :
    ∃ (n : ℕ) (e : (∐ fun _ : Fin n ↦ Spec (.of k)) ≅ X),
      e.hom ≫ p = Sigma.desc fun _ : Fin n ↦ 𝟙 (Spec (.of k)) := by sorry
