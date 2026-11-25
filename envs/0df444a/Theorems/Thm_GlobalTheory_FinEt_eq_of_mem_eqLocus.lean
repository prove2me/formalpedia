-- Prove2me | Theorems.Thm_GlobalTheory_FinEt_eq_of_mem_eqLocus
-- name    : GlobalTheory.FinEt.eq_of_mem_eqLocus
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:04:46.246742+00:00
-- url     : https://prove2.me/theorems/cd3177d3-d8a9-4f1c-bb3f-5992e379e4de
-- title:
--   Fin Et: eq of mem eq Locus
-- statement:
--   The Fin Et construction uses the eq of mem eq Locus property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsIsoIffBijectiveOverAlgClosed.lean#L706-L709
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsIsoIffBijectiveOverAlgClosed.lean#L706-L709

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

theorem GlobalTheory.FinEt.eq_of_mem_eqLocus [PreconnectedSpace S] (f g : X ⟶ Y)
    [IsFinite X.hom] [Etale X.hom] [IsFinite Y.hom] [Etale Y.hom] {s : S} (hs : s ∈ eqLocus f g) :
    f = g := by sorry
