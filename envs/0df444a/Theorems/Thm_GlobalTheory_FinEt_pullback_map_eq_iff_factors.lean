-- Prove2me | Theorems.Thm_GlobalTheory_FinEt_pullback_map_eq_iff_factors
-- name    : GlobalTheory.FinEt.pullback_map_eq_iff_factors
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T13:24:30.462192+00:00
-- url     : https://prove2.me/theorems/780acebd-921f-4903-9f71-52567a11e7da
-- title:
--   Fin Et: pullback map eq iff factors
-- statement:
--   The Fin Et construction uses the pullback map eq iff factors property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsIsoIffBijectiveOverAlgClosed.lean#L700-L704
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsIsoIffBijectiveOverAlgClosed.lean#L700-L704

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

theorem GlobalTheory.FinEt.pullback_map_eq_iff_factors {T : Scheme.{u}} (t : T ⟶ S) (f g : X ⟶ Y)
    [IsFinite X.hom] [Etale X.hom] [IsFinite Y.hom] [Etale Y.hom] :
    (Over.pullback t).map f = (Over.pullback t).map g ↔
      ∃ t' : T ⟶ eqLocusOpen f g, t' ≫ (eqLocusOpen f g).ι = t := by sorry
