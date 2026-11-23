-- Prove2me | Theorems.Thm_GlobalTheory_FinEt_isIso_iff_bijective_algClosed
-- name    : GlobalTheory.FinEt.isIso_iff_bijective_algClosed
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:10:24.114564+00:00
-- url     : https://prove2.me/theorems/07f044a3-9ecb-47d9-9e45-355438a7e39e
-- title:
--   Fin Et: is Iso iff bijective alg Closed
-- statement:
--   The Fin Et construction uses the is Iso iff bijective alg Closed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsIsoIffBijectiveOverAlgClosed.lean#L133-L167
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsIsoIffBijectiveOverAlgClosed.lean#L133-L167

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

theorem GlobalTheory.FinEt.isIso_iff_bijective_algClosed {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] [Etale f] :
    IsIso f ↔ ∀ (k : Type u) [Field k] [IsAlgClosed k],
      Function.Bijective fun x : Spec (.of k) ⟶ X ↦ x ≫ f := by sorry
