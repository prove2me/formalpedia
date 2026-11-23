-- Prove2me | Theorems.Thm_GlobalTheory_cubeFunctor_shortExact
-- name    : GlobalTheory.cubeFunctor_shortExact
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:51:02.356633+00:00
-- url     : https://prove2.me/theorems/8a66f59a-9e7c-4212-957a-38f313862d42
-- title:
--   Global Theory: cube Functor short Exact
-- statement:
--   The Global Theory construction uses the cube Functor short Exact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsIsoTermComparisonRestrictScalars.lean#L586-L590
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsIsoTermComparisonRestrictScalars.lean#L586-L590

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsIsoTermComparisonRestrictScalars
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits
universe v v' u u'
open GlobalTheory
variable {ι : Type} [LinearOrder ι] {R : Type u} [Ring R]

theorem GlobalTheory.cubeFunctor_shortExact (S : ShortComplex (Cube.{v} ι R))
    (hS : ∀ s : Finset ι, (S.map ((evaluation _ _).obj s)).ShortExact) :
    (S.map (cubeFunctor ι R)).ShortExact := by sorry
