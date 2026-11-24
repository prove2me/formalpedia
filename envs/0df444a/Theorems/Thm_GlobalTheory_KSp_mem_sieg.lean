-- Prove2me | Theorems.Thm_GlobalTheory_KSp_mem_sieg
-- name    : GlobalTheory.KSp.mem_sieg
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T21:09:51.957228+00:00
-- url     : https://prove2.me/theorems/8cb0b037-eef1-4942-98d4-02648f42d35b
-- title:
--   KSp: mem sieg
-- statement:
--   The KSp construction uses the mem sieg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/UnipVal.lean#L107-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/UnipVal.lean#L107-L108

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_KudlaSplittingSplitUnitary
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_UnipVal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix
open scoped Topology Classical
open GlobalTheory GlobalTheory.KSp
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
open GlobalTheory.SplitUnitary
variable {F : Type} [Field F] {E : Type} [Field E] [Algebra F E] (c : E →ₐ[F] E)
  {α ν : Type} [Fintype α] [DecidableEq α] [Fintype ν] [DecidableEq ν]

theorem GlobalTheory.KSp.mem_sieg {g : UG c (stdJ ν E)} : g ∈ sieg c ν ↔ (mat c g).toBlocks₂₁ = 0 := by sorry
