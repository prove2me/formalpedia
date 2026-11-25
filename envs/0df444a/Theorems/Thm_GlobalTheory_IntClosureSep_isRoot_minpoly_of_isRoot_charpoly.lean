-- Prove2me | Theorems.Thm_GlobalTheory_IntClosureSep_isRoot_minpoly_of_isRoot_charpoly
-- name    : GlobalTheory.IntClosureSep.isRoot_minpoly_of_isRoot_charpoly
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T00:26:05.299439+00:00
-- url     : https://prove2.me/theorems/992b0425-3f11-4ebb-a805-efbfe8495d6e
-- title:
--   Int Closure Sep: is Root minpoly of is Root charpoly
-- statement:
--   The Int Closure Sep construction uses the is Root minpoly of is Root charpoly property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IntegralClosureFgDvrOfSeparableCharpoly.lean#L9-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IntegralClosureFgDvrOfSeparableCharpoly.lean#L9-L35

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

theorem GlobalTheory.IntClosureSep.isRoot_minpoly_of_isRoot_charpoly {E A L : Type} [Field E] [CommRing A] [Algebra E A]
    [Module.Finite E A] [Field L] [Algebra E L] (g : A) {α : L}
    (hα : ((LinearMap.mulLeft E g).charpoly.map (algebraMap E L)).IsRoot α) :
    ((minpoly E g).map (algebraMap E L)).IsRoot α := by sorry
