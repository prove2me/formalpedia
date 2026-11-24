-- Prove2me | Theorems.Thm_GlobalTheory_FinEt_isIso_pullback_map_iff
-- name    : GlobalTheory.FinEt.isIso_pullback_map_iff
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T13:24:14.398959+00:00
-- url     : https://prove2.me/theorems/4b66d285-73b3-4d1e-81a9-e0a35599cd38
-- title:
--   Fin Et: is Iso pullback map iff
-- statement:
--   The Fin Et construction uses the is Iso pullback map iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsIsoIffBijectiveOverAlgClosed.lean#L95-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsIsoIffBijectiveOverAlgClosed.lean#L95-L107

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

theorem GlobalTheory.FinEt.isIso_pullback_map_iff {T : Scheme.{u}} (t : T ⟶ S) (f : X ⟶ Y)
    [IsFinite X.hom] [Etale X.hom] [IsFinite Y.hom] [Etale Y.hom] :
    IsIso ((Over.pullback t).map f) ↔ Set.range t ⊆ isoLocus f := by sorry
