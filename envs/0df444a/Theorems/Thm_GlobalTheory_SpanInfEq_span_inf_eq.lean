-- Prove2me | Theorems.Thm_GlobalTheory_SpanInfEq_span_inf_eq
-- name    : GlobalTheory.SpanInfEq.span_inf_eq
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T05:16:16.174902+00:00
-- url     : https://prove2.me/theorems/8ae146e2-bd31-58e5-8e89-0a454b57a895
-- title:
--   Span Inf Eq: span inf eq
-- statement:
--   The Span Inf Eq construction uses the span inf eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/SpanInfEq.lean#L38-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/SpanInfEq.lean#L38-L59

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SpanInfEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.SpanInfEq
open NumberField

theorem GlobalTheory.SpanInfEq.span_inf_eq {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V]
    [Module K V] [Module (RingOfIntegers K) V] [IsScalarTower (RingOfIntegers K) K V]
    (L : Submodule (RingOfIntegers K) V) (hL : Submodule.IsLattice K L) (T : Submodule K V) :
    Submodule.span K (↑(L ⊓ Submodule.restrictScalars (RingOfIntegers K) T) : Set V) = T := by sorry
