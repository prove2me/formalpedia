-- Prove2me | Theorems.Thm_GlobalTheory_cechFunctor_shortExact
-- name    : GlobalTheory.cechFunctor_shortExact
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:03:24.004277+00:00
-- url     : https://prove2.me/theorems/6f9909e7-ec6b-424a-acf3-6c01f2b2a3ac
-- title:
--   Global Theory: cech Functor short Exact
-- statement:
--   The Global Theory construction uses the cech Functor short Exact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsIsoTermComparisonRestrictScalars.lean#L592-L596
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsIsoTermComparisonRestrictScalars.lean#L592-L596

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

theorem GlobalTheory.cechFunctor_shortExact (S : ShortComplex (Cube.{v} ι R))
    (hS : ∀ s : Finset ι, s.Nonempty → (S.map ((evaluation _ _).obj s)).ShortExact) :
    (S.map (cechFunctor ι R)).ShortExact := by sorry
