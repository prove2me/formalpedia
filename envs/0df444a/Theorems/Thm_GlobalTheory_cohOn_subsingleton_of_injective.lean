-- Prove2me | Theorems.Thm_GlobalTheory_cohOn_subsingleton_of_injective
-- name    : GlobalTheory.cohOn.subsingleton_of_injective
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:44:22.103649+00:00
-- url     : https://prove2.me/theorems/adef664e-b051-4f1e-b3a7-8481bbb30640
-- title:
--   coh On: subsingleton of injective
-- statement:
--   The coh On construction uses the subsingleton of injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/HdimEqZeroOfSubsingleton.lean#L246-L248
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/HdimEqZeroOfSubsingleton.lean#L246-L248

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ToAbSheafPreservesFiniteLimits
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_HdimEqZeroOfSubsingleton
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits
universe t v u
noncomputable section
open GlobalTheory
variable {X : Scheme.{u}}
open GlobalTheory.cohOn

theorem GlobalTheory.cohOn.subsingleton_of_injective (F : X.Modules) [Injective ((toAbSheaf X).obj F)] (U : X.Opens)
    (n : ℕ) : Subsingleton (cohOn F U (n + 1)) := by sorry
