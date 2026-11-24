-- Prove2me | Theorems.Thm_GlobalTheory_FibSurj_fibMap_fst
-- name    : GlobalTheory.FibSurj.fibMap_fst
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T13:23:23.347954+00:00
-- url     : https://prove2.me/theorems/55fecb35-5d2e-4984-8e86-9dfce2881463
-- title:
--   Fib Surj: fib Map fst
-- statement:
--   The Fib Surj construction uses the fib Map fst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SpecialFibreConnectedOfBaseChange.lean#L28-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SpecialFibreConnectedOfBaseChange.lean#L28-L29

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

theorem GlobalTheory.FibSurj.fibMap_fst : fibMap φ s ≫ pullback.fst _ _ = pullback.fst _ _ ≫ pullback.fst _ _ := by sorry
