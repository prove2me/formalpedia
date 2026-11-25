-- Prove2me | Theorems.Thm_GlobalTheory_FinEt_isIso_of_mem_isoLocus
-- name    : GlobalTheory.FinEt.isIso_of_mem_isoLocus
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:04:38.736311+00:00
-- url     : https://prove2.me/theorems/c0f1ff68-af38-52ee-b31c-31c72d65354b
-- title:
--   Fin Et: is Iso of mem iso Locus
-- statement:
--   The Fin Et construction uses the is Iso of mem iso Locus property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsIsoIffBijectiveOverAlgClosed.lean#L711-L714
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsIsoIffBijectiveOverAlgClosed.lean#L711-L714

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

theorem GlobalTheory.FinEt.isIso_of_mem_isoLocus [PreconnectedSpace S] (f : X ⟶ Y)
    [IsFinite X.hom] [Etale X.hom] [IsFinite Y.hom] [Etale Y.hom] {s : S} (hs : s ∈ isoLocus f) :
    IsIso f := by sorry
