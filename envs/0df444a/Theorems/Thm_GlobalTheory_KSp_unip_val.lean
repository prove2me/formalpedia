-- Prove2me | Theorems.Thm_GlobalTheory_KSp_unip_val
-- name    : GlobalTheory.KSp.unip_val
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:11:53.829223+00:00
-- url     : https://prove2.me/theorems/ad1b9b9e-1b83-5085-8db8-a56b3faa30c3
-- title:
--   KSp: unip val
-- statement:
--   The KSp construction uses the unip val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/UnipVal.lean#L73-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/UnipVal.lean#L73-L74

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

theorem GlobalTheory.KSp.unip_val (b : Matrix ν ν E) (hb : (b.map c)ᵀ = b) :
    ((unip c b hb : GL (ν ⊕ ν) E) : Matrix (ν ⊕ ν) (ν ⊕ ν) E) = fromBlocks 1 b 0 1 := by sorry
