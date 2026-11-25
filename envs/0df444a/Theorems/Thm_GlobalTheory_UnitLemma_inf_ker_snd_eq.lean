-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_inf_ker_snd_eq
-- name    : GlobalTheory.UnitLemma.inf_ker_snd_eq
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T05:07:19.48439+00:00
-- url     : https://prove2.me/theorems/da00d545-37c0-4c8f-8107-e8a95d724d04
-- title:
--   Unit Lemma: inf ker snd eq
-- statement:
--   The Unit Lemma construction uses the inf ker snd eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NcardFibreStableLatticePairProjection.lean#L17-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NcardFibreStableLatticePairProjection.lean#L17-L29

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ComapInlMemStLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CardStableLatticesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NcardFibreStableLatticePairProjection
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma
open Polynomial
variable {O E A₁ A₂ : Type} [CommRing O] [Field E] [Algebra O E]
  [CommRing A₁] [CommRing A₂] [Algebra O A₁] [Algebra O A₂] [Algebra E A₁] [Algebra E A₂]
  [IsScalarTower O E A₁] [IsScalarTower O E A₂]

theorem GlobalTheory.UnitLemma.inf_ker_snd_eq (M : Submodule O (A₁ × A₂)) :
    M ⊓ LinearMap.ker (LinearMap.snd O A₁ A₂) =
      (M.comap (LinearMap.inl O A₁ A₂)).map (LinearMap.inl O A₁ A₂) := by sorry
