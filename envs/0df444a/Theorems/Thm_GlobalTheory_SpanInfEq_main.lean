-- Prove2me | Theorems.Thm_GlobalTheory_SpanInfEq_main
-- name    : GlobalTheory.SpanInfEq.main
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T05:16:28.723068+00:00
-- url     : https://prove2.me/theorems/6c83afca-7933-42ac-a860-502c40c697c2
-- title:
--   Span Inf Eq: main
-- statement:
--   The Span Inf Eq construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/SpanInfEq.lean#L61-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/SpanInfEq.lean#L61-L67

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

theorem GlobalTheory.SpanInfEq.main : ∀ {K : Type} [inst : Field K] [NumberField K] {V : Type} [inst_2 : AddCommGroup V]
    [inst_3 : Module K V] [inst_4 : Module (NumberField.RingOfIntegers K) V]
    [inst_5 : IsScalarTower (NumberField.RingOfIntegers K) K V]
    (L : Submodule (NumberField.RingOfIntegers K) V), Submodule.IsLattice K L →
    ∀ (T : Submodule K V),
    Submodule.span K (↑(L ⊓ Submodule.restrictScalars (NumberField.RingOfIntegers K) T) : Set V) = T := by sorry
