-- Prove2me | Theorems.Thm_GlobalTheory_FibSurj_fibre_connected_of_base_change
-- name    : GlobalTheory.FibSurj.fibre_connected_of_base_change
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T13:23:21.708733+00:00
-- url     : https://prove2.me/theorems/ac637fbc-c0c1-46e1-b0c4-752198a8076f
-- title:
--   Fib Surj: fibre connected of base change
-- statement:
--   The Fib Surj construction uses the fibre connected of base change property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SpecialFibreConnectedOfBaseChange.lean#L55-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SpecialFibreConnectedOfBaseChange.lean#L55-L59

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_SpecialFibreUnits
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SpecialFibreConnectedOfBaseChange
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry
open GlobalTheory GlobalTheory.FibSurj
open IsLocalRing

theorem GlobalTheory.FibSurj.fibre_connected_of_base_change :
  ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (φ : V →+* O), IsLocalHom φ → ∀ (X : Scheme.{0}) (s : X ⟶ Spec (.of V)), ConnectedSpace ↑(GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits.specialFibre (pullback.snd s (Spec.map (CommRingCat.ofHom φ)))) → ConnectedSpace ↑(GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits.specialFibre s) := by sorry
