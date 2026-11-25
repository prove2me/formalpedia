-- Prove2me | Theorems.Thm_GlobalTheory_CohenRegular_exists_of_coefficientField
-- name    : GlobalTheory.CohenRegular.exists_of_coefficientField
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T00:13:42.236558+00:00
-- url     : https://prove2.me/theorems/4e1bd81e-95c3-4253-96eb-4b0ccb406366
-- title:
--   Cohen Regular: exists of coefficient Field
-- statement:
--   The Cohen Regular construction uses the exists of coefficient Field property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsCoefficientFieldOfCharZero.lean#L120-L166
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsCoefficientFieldOfCharZero.lean#L120-L166

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

theorem GlobalTheory.CohenRegular.exists_of_coefficientField (S : Type) [CommRing S] [IsDomain S] [IsLocalRing S]
    [IsNoetherianRing S] [hc : IsAdicComplete (maximalIdeal S) S] (Λ : Subring S) (hF : IsField Λ)
    (h1 : ∀ s : S, ∃ a ∈ Λ, s - a ∈ maximalIdeal S) :
    ∃ (A : Type) (_ : CommRing A) (_ : IsRegularLocalRing A) (i : A →+* S),
      Function.Injective i ∧ i.Finite := by sorry
