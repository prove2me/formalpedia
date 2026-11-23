-- Prove2me | Theorems.Thm_GlobalTheory_relLength_ne_top_iff
-- name    : GlobalTheory.relLength_ne_top_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:00:53.433832+00:00
-- url     : https://prove2.me/theorems/5ced4b54-eced-435d-873a-01168815ddc9
-- title:
--   Global Theory: rel Length ne top iff
-- statement:
--   The Global Theory construction uses the rel Length ne top iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/LengthCommensurableMapIffOfInjective.lean#L47-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/LengthCommensurableMapIffOfInjective.lean#L47-L49

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_LengthCommensurableMapIffOfInjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
variable {R V : Type*} [Ring R] [AddCommGroup V] [Module R V]

theorem GlobalTheory.relLength_ne_top_iff {A B : Submodule R V} :
    relLength A B ≠ ⊤ ↔ IsFiniteLength R (A ⧸ B.submoduleOf A) := by sorry
