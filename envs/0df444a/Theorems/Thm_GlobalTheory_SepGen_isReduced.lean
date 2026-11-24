-- Prove2me | Theorems.Thm_GlobalTheory_SepGen_isReduced
-- name    : GlobalTheory.SepGen.isReduced
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:04:36.77882+00:00
-- url     : https://prove2.me/theorems/bea40174-cb09-491b-a1ef-b5fdf36d18b2
-- title:
--   Sep Gen: is Reduced
-- statement:
--   The Sep Gen construction uses the is Reduced property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AdjoinEqTopAndIsReducedOfCharpolySeparable.lean#L48-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AdjoinEqTopAndIsReducedOfCharpolySeparable.lean#L48-L57

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

theorem GlobalTheory.SepGen.isReduced (y : A) (hs : (LinearMap.mulLeft E y).charpoly.Separable) : IsReduced A := by sorry
