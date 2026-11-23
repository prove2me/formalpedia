-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_isIntegral_of_isLat_stable
-- name    : GlobalTheory.UnitLemma.isIntegral_of_isLat_stable
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:32:00.363345+00:00
-- url     : https://prove2.me/theorems/dcde2965-96b2-4d5b-a11f-ae10059867e6
-- title:
--   Unit Lemma: is Integral of is Lat stable
-- statement:
--   The Unit Lemma construction uses the is Integral of is Lat stable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/KappaSumZeroAndStableSumMulZeroOfNotIntegral.lean#L10-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/KappaSumZeroAndStableSumMulZeroOfNotIntegral.lean#L10-L37

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_KappaSumZeroAndStableSumMulZeroOfNotIntegral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Polynomial
open GlobalTheory GlobalTheory.UnitLemma
open Polynomial

theorem GlobalTheory.UnitLemma.isIntegral_of_isLat_stable {O E A : Type} [CommRing O] [Field E] [CommRing A] [Algebra O A]
    [Algebra E A] (L : Submodule O A) (hL : _root_.GlobalTheory.UnitLemma.IsLat O E L) (g : A) (hg : ∀ y ∈ L, g * y ∈ L) :
    IsIntegral O g := by sorry
