-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_PairStab_intUnits_prod_eq
-- name    : GlobalTheory.UnitLemma.PairStab.intUnits_prod_eq
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:05:48.376767+00:00
-- url     : https://prove2.me/theorems/debcc70f-6dcf-4024-b7b2-f68c24ea3813
-- title:
--   Pair Stab: int Units prod eq
-- statement:
--   The Pair Stab construction uses the int Units prod eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/StabilizerStableLatticePairRelIndexIntegralUnits.lean#L23-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/StabilizerStableLatticePairRelIndexIntegralUnits.lean#L23-L31

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

theorem GlobalTheory.UnitLemma.PairStab.intUnits_prod_eq :
    intUnits O (A₁ × A₂) = ((intUnits O A₁).prod (intUnits O A₂)).comap
      (MulEquiv.prodUnits (M := A₁) (N := A₂)).toMonoidHom := by sorry
