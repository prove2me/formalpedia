-- Prove2me | Theorems.Thm_GlobalTheory_NB_LT_algHom_coe
-- name    : GlobalTheory.NB.LT.algHom_coe
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T18:30:00.901395+00:00
-- url     : https://prove2.me/theorems/d3b0413d-e5a7-4f85-ac30-05b3e2b68b6f
-- title:
--   LT: alg Hom coe
-- statement:
--   The LT construction uses the alg Hom coe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/DvdSubOfDvdSubX.lean#L89-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/DvdSubOfDvdSubX.lean#L89-L93

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DvdSubOfDvdSubX
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PowerSeries
open GlobalTheory GlobalTheory.NB GlobalTheory.NB.LT
variable {R S : Type} [CommRing R] [CommRing S] {l : ℕ}
open PowerSeries
variable {R S : Type} [CommRing R] [CommRing S] {l : ℕ}

theorem GlobalTheory.NB.LT.algHom_coe {B : Type} [CommRing B] [Algebra R B] (σ : R⟦X⟧ →ₐ[R] B) (r : Polynomial R) :
    σ (r : R⟦X⟧) = Polynomial.aeval (σ X) r := by sorry
