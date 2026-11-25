-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_stabilizer_eq_of_mem_orbit
-- name    : GlobalTheory.UnitLemma.stabilizer_eq_of_mem_orbit
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T07:49:53.37436+00:00
-- url     : https://prove2.me/theorems/c1434575-9ccf-5b1d-925f-9a2141c8f571
-- title:
--   Unit Lemma: stabilizer eq of mem orbit
-- statement:
--   The Unit Lemma construction uses the stabilizer eq of mem orbit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/StableLatticeOrbitCountEqSumOrbits.lean#L46-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/StableLatticeOrbitCountEqSumOrbits.lean#L46-L51

import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ComapInlMemStLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_StableLatticeOrbitCountEqSumOrbits
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Polynomial
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma
variable {O E A : Type} [CommRing O] [Field E] [CommRing A] [Algebra O A] [Algebra E A]

theorem GlobalTheory.UnitLemma.stabilizer_eq_of_mem_orbit (g : A) {x y : stLat O E g} (h : y ∈ MulAction.orbit Aˣ x) :
    MulAction.stabilizer Aˣ y = MulAction.stabilizer Aˣ x := by sorry
