-- Prove2me | Theorems.Thm_GlobalTheory_SepGen_adjoin_eq_top
-- name    : GlobalTheory.SepGen.adjoin_eq_top
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:40:14.02492+00:00
-- url     : https://prove2.me/theorems/796b3404-3bea-4cc9-b618-87c19c3d2763
-- title:
--   Sep Gen: adjoin eq top
-- statement:
--   The Sep Gen construction uses the adjoin eq top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AdjoinEqTopAndIsReducedOfCharpolySeparable.lean#L36-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AdjoinEqTopAndIsReducedOfCharpolySeparable.lean#L36-L46

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

theorem GlobalTheory.SepGen.adjoin_eq_top (y : A) (hs : (LinearMap.mulLeft E y).charpoly.Separable) :
    Algebra.adjoin E ({y} : Set A) = ⊤ := by sorry
