-- Prove2me | Theorems.Thm_GlobalTheory_FinEt_card_points_eq_finrank
-- name    : GlobalTheory.FinEt.card_points_eq_finrank
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T13:23:56.630242+00:00
-- url     : https://prove2.me/theorems/de734276-5525-4b17-94b5-d8683c4ddb7c
-- title:
--   Fin Et: card points eq finrank
-- statement:
--   The Fin Et construction uses the card points eq finrank property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsIsoIffBijectiveOverAlgClosed.lean#L651-L679
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsIsoIffBijectiveOverAlgClosed.lean#L651-L679

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

theorem GlobalTheory.FinEt.card_points_eq_finrank {X S : Scheme.{u}} (p : X ⟶ S) [IsFinite p] [Etale p]
    {k : Type u} [Field k] [IsSepClosed k] (t : Spec (.of k) ⟶ S) (z : Spec (.of k)) :
    Finite {x : Spec (.of k) ⟶ X // x ≫ p = t} ∧
      Nat.card {x : Spec (.of k) ⟶ X // x ≫ p = t} = p.finrank (t z) := by sorry
