-- Prove2me | Theorems.Thm_GlobalTheory_Cube_term_shortExact
-- name    : GlobalTheory.Cube.term_shortExact
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:31:59.660297+00:00
-- url     : https://prove2.me/theorems/1c27872e-3e91-425a-81e1-cf577ff112d7
-- title:
--   Cube: term short Exact
-- statement:
--   The Cube construction uses the term short Exact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsIsoTermComparisonRestrictScalars.lean#L564-L584
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsIsoTermComparisonRestrictScalars.lean#L564-L584

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

theorem GlobalTheory.Cube.term_shortExact (S : ShortComplex (Cube.{v} ι R)) (p : ℕ)
    (hS : ∀ s : Finset ι, s.card = p → (S.map ((evaluation _ _).obj s)).ShortExact) :
    ((S.map (cubeFunctor ι R)).map (HomologicalComplex.eval _ _ p)).ShortExact := by sorry
