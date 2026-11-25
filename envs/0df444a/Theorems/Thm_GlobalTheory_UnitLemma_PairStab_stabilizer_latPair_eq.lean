-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_PairStab_stabilizer_latPair_eq
-- name    : GlobalTheory.UnitLemma.PairStab.stabilizer_latPair_eq
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T05:07:31.021794+00:00
-- url     : https://prove2.me/theorems/af17ea1d-867b-4097-a849-e136269fcbec
-- title:
--   Pair Stab: stabilizer lat Pair eq
-- statement:
--   The Pair Stab construction uses the stabilizer lat Pair eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/StabilizerStableLatticePairRelIndexIntegralUnits.lean#L35-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/StabilizerStableLatticePairRelIndexIntegralUnits.lean#L35-L41

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ComapInlMemStLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_StabilizerStableLatticePairRelIndexIntegralUnits
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.PairStab
open GlobalTheory.UnitLemma Polynomial
variable (O : Type) [CommRing O] {A₁ A₂ : Type} [CommRing A₁] [CommRing A₂] [Algebra O A₁] [Algebra O A₂]
variable (E : Type) [Field E] [Algebra E A₁] [Algebra E A₂]

theorem GlobalTheory.UnitLemma.PairStab.stabilizer_latPair_eq (g₁ : A₁) (g₂ : A₂) (y : LatPair O E g₁ g₂) :
    MulAction.stabilizer (A₁ × A₂)ˣ y = ((MulAction.stabilizer A₁ˣ y.1).prod
      (MulAction.stabilizer A₂ˣ y.2)).comap (MulEquiv.prodUnits (M := A₁) (N := A₂)).toMonoidHom := by sorry
