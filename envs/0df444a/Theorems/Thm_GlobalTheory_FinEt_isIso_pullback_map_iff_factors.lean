-- Prove2me | Theorems.Thm_GlobalTheory_FinEt_isIso_pullback_map_iff_factors
-- name    : GlobalTheory.FinEt.isIso_pullback_map_iff_factors
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T13:24:07.421801+00:00
-- url     : https://prove2.me/theorems/b1cb0d80-d42f-4941-99f2-8c5dc2a4db48
-- title:
--   Fin Et: is Iso pullback map iff factors
-- statement:
--   The Fin Et construction uses the is Iso pullback map iff factors property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsIsoIffBijectiveOverAlgClosed.lean#L695-L698
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsIsoIffBijectiveOverAlgClosed.lean#L695-L698

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

theorem GlobalTheory.FinEt.isIso_pullback_map_iff_factors {T : Scheme.{u}} (t : T ⟶ S) (f : X ⟶ Y)
    [IsFinite X.hom] [Etale X.hom] [IsFinite Y.hom] [Etale Y.hom] :
    IsIso ((Over.pullback t).map f) ↔ ∃ t' : T ⟶ isoLocusOpen f, t' ≫ (isoLocusOpen f).ι = t := by sorry
