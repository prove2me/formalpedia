-- Prove2me | Theorems.Thm_GlobalTheory_FinEt_finrank_eq_add
-- name    : GlobalTheory.FinEt.finrank_eq_add
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:10:20.562724+00:00
-- url     : https://prove2.me/theorems/dc9ae159-28e2-4750-a96f-3340f84dec93
-- title:
--   Fin Et: finrank eq add
-- statement:
--   The Fin Et construction uses the finrank eq add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsIsoIffBijectiveOverAlgClosed.lean#L304-L362
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsIsoIffBijectiveOverAlgClosed.lean#L304-L362

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

theorem GlobalTheory.FinEt.finrank_eq_add {U V X S : Scheme.{u}} (i : U ⟶ X) (j : V ⟶ X) [IsOpenImmersion i]
    [IsOpenImmersion j] (h : Set.range j = (Set.range i)ᶜ) (p : X ⟶ S) [IsFinite p] [Flat p]
    (s : S) : p.finrank s = (i ≫ p).finrank s + (j ≫ p).finrank s := by sorry
