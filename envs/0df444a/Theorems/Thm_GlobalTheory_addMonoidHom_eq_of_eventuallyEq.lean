-- Prove2me | Theorems.Thm_GlobalTheory_addMonoidHom_eq_of_eventuallyEq
-- name    : GlobalTheory.addMonoidHom_eq_of_eventuallyEq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:03:31.834804+00:00
-- url     : https://prove2.me/theorems/0f789a90-e326-4a62-b5be-c9e6b01f38d1
-- title:
--   Global Theory: add Monoid Hom eq of eventually Eq
-- statement:
--   The Global Theory construction uses the add Monoid Hom eq of eventually Eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/TendstoUniformlyOnDoublingLogOfContraction.lean#L185-L191
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/TendstoUniformlyOnDoublingLogOfContraction.lean#L185-L191

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_TendstoUniformlyOnDoublingLogOfContraction
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Metric Set Filter Asymptotics
open scoped Topology
open GlobalTheory
variable {V A : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [AddCommGroup A]

theorem GlobalTheory.addMonoidHom_eq_of_eventuallyEq {e e' : V →+ A} (h : e =ᶠ[𝓝 0] e') : e = e' := by sorry
