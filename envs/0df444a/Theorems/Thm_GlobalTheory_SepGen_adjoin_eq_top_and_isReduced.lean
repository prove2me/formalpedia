-- Prove2me | Theorems.Thm_GlobalTheory_SepGen_adjoin_eq_top_and_isReduced
-- name    : GlobalTheory.SepGen.adjoin_eq_top_and_isReduced
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T19:53:20.453848+00:00
-- url     : https://prove2.me/theorems/7764c6b1-e533-4ee2-b647-e956f6b150c4
-- title:
--   Sep Gen: adjoin eq top and is Reduced
-- statement:
--   The Sep Gen construction uses the adjoin eq top and is Reduced property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AdjoinEqTopAndIsReducedOfCharpolySeparable.lean#L59-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AdjoinEqTopAndIsReducedOfCharpolySeparable.lean#L59-L62

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_EqZeroOfNotPrimary
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AdjoinEqTopAndIsReducedOfCharpolySeparable
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory GlobalTheory.SepGen
variable {E : Type} [Field E] {A : Type} [CommRing A] [Algebra E A] [Module.Finite E A]

theorem GlobalTheory.SepGen.adjoin_eq_top_and_isReduced : ∀ (E A : Type) [Field E] [CommRing A] [Algebra E A]
    [Module.Finite E A] (y : A), (LinearMap.mulLeft E y).charpoly.Separable →
    Algebra.adjoin E ({y} : Set A) = ⊤ ∧ IsReduced A := by sorry
