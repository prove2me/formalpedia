-- Prove2me | Theorems.Thm_GlobalTheory_CohenRegular_exists_finite_over_regular
-- name    : GlobalTheory.CohenRegular.exists_finite_over_regular
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T11:59:59.488215+00:00
-- url     : https://prove2.me/theorems/befa29de-905d-4c80-ba83-e875a8d330cc
-- title:
--   Cohen Regular: exists finite over regular
-- statement:
--   The Cohen Regular construction uses the exists finite over regular property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsCoefficientFieldOfCharZero.lean#L219-L234
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsCoefficientFieldOfCharZero.lean#L219-L234

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_CohenStructureFiniteOverNormalCompleteSubring
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsCoefficientFieldOfCharZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory GlobalTheory.CohenRegular
open MvPowerSeries GlobalTheory.CohenStructure

theorem GlobalTheory.CohenRegular.exists_finite_over_regular :
    ∀ (S : Type) [CommRing S] [IsDomain S] [IsLocalRing S] [IsNoetherianRing S]
      [IsAdicComplete (IsLocalRing.maximalIdeal S) S],
      ∃ (A : Type) (_ : CommRing A) (_ : IsRegularLocalRing A) (i : A →+* S),
        Function.Injective i ∧ i.Finite := by sorry
