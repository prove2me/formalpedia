-- Prove2me | Theorems.Thm_GlobalTheory_FormalAlg_IsSystem_baseIdeal_le
-- name    : GlobalTheory.FormalAlg.IsSystem.baseIdeal_le
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:06:31.223635+00:00
-- url     : https://prove2.me/theorems/cc398597-a7f8-5ea0-a9c4-32b2570c9502
-- title:
--   Is System: base Ideal le
-- statement:
--   The Is System construction uses the base Ideal le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/BaseIdealIdeal.lean#L37-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/BaseIdealIdeal.lean#L37-L40

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThickTransComp
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_BaseIdealIdeal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open GlobalTheory.AbLaw
open GlobalTheory GlobalTheory.FormalAlg
variable {R : Type} [CommRing R] {W : Scheme.{0}}

theorem GlobalTheory.FormalAlg.IsSystem.baseIdeal_le {f : W ⟶ Spec (CommRingCat.of R)} {I : Ideal R}
    {t : ℕ → W.IdealSheafData} (h : IsSystem f I t) (e : ℕ) : baseIdeal f (I ^ (e + 1)) ≤ t e := by sorry
