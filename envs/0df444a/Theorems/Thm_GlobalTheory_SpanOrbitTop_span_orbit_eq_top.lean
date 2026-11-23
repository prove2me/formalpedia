-- Prove2me | Theorems.Thm_GlobalTheory_SpanOrbitTop_span_orbit_eq_top
-- name    : GlobalTheory.SpanOrbitTop.span_orbit_eq_top
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:49:28.502945+00:00
-- url     : https://prove2.me/theorems/590958c9-6319-488a-bd6f-4d2ca2290e27
-- title:
--   Span Orbit Top: span orbit eq top
-- statement:
--   The Span Orbit Top construction uses the span orbit eq top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/SpanOrbitEqTop.lean#L5-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/SpanOrbitEqTop.lean#L5-L24

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SpanOrbitEqTop
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.SpanOrbitTop

theorem GlobalTheory.SpanOrbitTop.span_orbit_eq_top {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ G V) (hπ : Representation.IsIrreducible π) {v : V} (hv : v ≠ 0) :
    Submodule.span ℂ (Set.range fun g : G ↦ π g v) = ⊤ := by sorry
