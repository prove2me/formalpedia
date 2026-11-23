-- Prove2me | Theorems.Thm_GlobalTheory_FinEt_exists_algClosed_point
-- name    : GlobalTheory.FinEt.exists_algClosed_point
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:11:19.765212+00:00
-- url     : https://prove2.me/theorems/921e7d0e-06b5-48ee-9baa-ce644ca833d1
-- title:
--   Fin Et: exists alg Closed point
-- statement:
--   The Fin Et construction uses the exists alg Closed point property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsIsoIffBijectiveOverAlgClosed.lean#L19-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsIsoIffBijectiveOverAlgClosed.lean#L19-L33

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

theorem GlobalTheory.FinEt.exists_algClosed_point (X : Scheme.{u}) (x : X) :
    ∃ (k : Type u) (_ : Field k) (_ : IsAlgClosed k) (a : Spec (.of k) ⟶ X),
      Set.range a = {x} := by sorry
