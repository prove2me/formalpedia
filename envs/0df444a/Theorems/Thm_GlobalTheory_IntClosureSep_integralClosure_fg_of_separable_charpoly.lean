-- Prove2me | Theorems.Thm_GlobalTheory_IntClosureSep_integralClosure_fg_of_separable_charpoly
-- name    : GlobalTheory.IntClosureSep.integralClosure_fg_of_separable_charpoly
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T00:25:24.553508+00:00
-- url     : https://prove2.me/theorems/363f3060-7697-493a-b11e-5fec11d2a8b2
-- title:
--   Int Closure Sep: integral Closure fg of separable charpoly
-- statement:
--   The Int Closure Sep construction uses the integral Closure fg of separable charpoly property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IntegralClosureFgDvrOfSeparableCharpoly.lean#L37-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IntegralClosureFgDvrOfSeparableCharpoly.lean#L37-L118

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_NatCardAlgHomEqFinrankOfIsReducedOfIsFractionRin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IntegralClosureFgDvrOfSeparableCharpoly
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Polynomial Module
open GlobalTheory GlobalTheory.IntClosureSep

theorem GlobalTheory.IntClosureSep.integralClosure_fg_of_separable_charpoly : ∀ (O E A : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field E] [Algebra O E] [IsFractionRing O E] [CommRing A] [Algebra O A] [Algebra E A] [IsScalarTower O E A] [Module.Finite E A] (g : A), (LinearMap.mulLeft E g).charpoly.Separable → (Subalgebra.toSubmodule (integralClosure O A)).FG := by sorry
