-- Prove2me | Theorems.Thm_GlobalTheory_FinEt_range_subset_iff_factors
-- name    : GlobalTheory.FinEt.range_subset_iff_factors
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:10:20.906201+00:00
-- url     : https://prove2.me/theorems/29035fda-91f8-4fe8-ad8e-865f75105823
-- title:
--   Fin Et: range subset iff factors
-- statement:
--   The Fin Et construction uses the range subset iff factors property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsIsoIffBijectiveOverAlgClosed.lean#L281-L288
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsIsoIffBijectiveOverAlgClosed.lean#L281-L288

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

theorem GlobalTheory.FinEt.range_subset_iff_factors {T : Scheme.{u}} (t : T ⟶ S) (U : S.Opens) :
    Set.range t ⊆ U ↔ ∃ t' : T ⟶ U, t' ≫ U.ι = t := by sorry
