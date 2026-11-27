-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_OrthoSelfDual_span_selfDual
-- name    : GlobalTheory.UnitLemma.OrthoSelfDual.span_selfDual
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:42:19.787928+00:00
-- url     : https://prove2.me/theorems/b3c56721-93f8-5e56-ba59-fcaa47a6d8ad
-- title:
--   Ortho Self Dual: span self Dual
-- statement:
--   The Ortho Self Dual construction uses the span self Dual property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/SpanSelfDual.lean#L62-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/SpanSelfDual.lean#L62-L92

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SpanSelfDual
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Matrix MeasureTheory
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.OrthoSelfDual

theorem GlobalTheory.UnitLemma.OrthoSelfDual.span_selfDual (K : UQ) (B : InvAlg K) (x : B.A) (n : ℕ) (e : Module.Basis (Fin n) K.E B.A)
    (h : ∀ i j, B.herm x (e i) (e j) = if i = j then 1 else 0) (y : B.A) :
    y ∈ Submodule.span K.O (Set.range e) ↔
      ∀ z ∈ Submodule.span K.O (Set.range e), B.herm x y z ∈ (algebraMap K.O K.E).range := by sorry
