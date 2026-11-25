-- Prove2me | Theorems.Thm_GlobalTheory_CohenRegular_exists_of_mixed
-- name    : GlobalTheory.CohenRegular.exists_of_mixed
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T00:13:11.153347+00:00
-- url     : https://prove2.me/theorems/966f8330-862d-4657-9336-7e86f1ed54d9
-- title:
--   Cohen Regular: exists of mixed
-- statement:
--   The Cohen Regular construction uses the exists of mixed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsCoefficientFieldOfCharZero.lean#L168-L217
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsCoefficientFieldOfCharZero.lean#L168-L217

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

theorem GlobalTheory.CohenRegular.exists_of_mixed (S : Type) [CommRing S] [IsDomain S] [IsLocalRing S]
    [IsNoetherianRing S] [hc : IsAdicComplete (maximalIdeal S) S] {p : ℕ} (hp : p.Prime)
    (h0 : (p : S) ∈ maximalIdeal S) (hp0 : (p : S) ≠ 0) :
    ∃ (A : Type) (_ : CommRing A) (_ : IsRegularLocalRing A) (i : A →+* S),
      Function.Injective i ∧ i.Finite := by sorry
