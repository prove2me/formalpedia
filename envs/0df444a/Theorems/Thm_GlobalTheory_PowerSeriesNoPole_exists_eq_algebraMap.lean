-- Prove2me | Theorems.Thm_GlobalTheory_PowerSeriesNoPole_exists_eq_algebraMap
-- name    : GlobalTheory.PowerSeriesNoPole.exists_eq_algebraMap
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:16:07.578618+00:00
-- url     : https://prove2.me/theorems/da6d959a-2f23-4fee-aee3-cdaa97bc6006
-- title:
--   Power Series No Pole: exists eq algebra Map
-- statement:
--   The Power Series No Pole construction uses the exists eq algebra Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsPowerSeriesOfNoPoleAwayUniformizerX.lean#L39-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsPowerSeriesOfNoPoleAwayUniformizerX.lean#L39-L89

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsPowerSeriesOfNoPoleAwayUniformizerX
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped LaurentSeries
open GlobalTheory GlobalTheory.PowerSeriesNoPole
open scoped LaurentSeries
open PowerSeries

theorem GlobalTheory.PowerSeriesNoPole.exists_eq_algebraMap (A : Type) [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A]
    (ϖ : A) (hϖ : Irreducible ϖ) (k : A →+* ℂ) (hk : Function.Injective k)
    (S : Type) [CommRing S] [Algebra (PowerSeries A) S]
    [IsLocalization.Away (PowerSeries.C ϖ * PowerSeries.X : PowerSeries A) S]
    (ι : S →+* ℂ⸨X⸩)
    (hι : ∀ s : PowerSeries A,
      ι (algebraMap _ S s) = HahnSeries.ofPowerSeries ℤ ℂ (PowerSeries.map k s))
    (v : S) (hv : ι v ∈ (HahnSeries.ofPowerSeries ℤ ℂ).range)
    (hst : ∃ s t : PowerSeries A, ¬ PowerSeries.C ϖ ∣ t ∧
      v * algebraMap _ S t = algebraMap _ S s) :
    ∃ s : PowerSeries A, v = algebraMap _ S s := by sorry
