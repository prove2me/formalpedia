-- Prove2me | Theorems.Thm_GlobalTheory_FibSurj_fibMap_surjective
-- name    : GlobalTheory.FibSurj.fibMap_surjective
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T13:23:19.79127+00:00
-- url     : https://prove2.me/theorems/e9f8b1f3-4ccd-4fd6-9026-7b3f9df9aac5
-- title:
--   Fib Surj: fib Map surjective
-- statement:
--   The Fib Surj construction uses the fib Map surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SpecialFibreConnectedOfBaseChange.lean#L45-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SpecialFibreConnectedOfBaseChange.lean#L45-L51

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
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (φ : V →+* O) [IsLocalHom φ]
  {X : Scheme.{0}} (s : X ⟶ Spec (.of V))

theorem GlobalTheory.FibSurj.fibMap_surjective : Surjective (fibMap φ s) := by sorry
