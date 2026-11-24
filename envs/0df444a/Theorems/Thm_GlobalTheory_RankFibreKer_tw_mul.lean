-- Prove2me | Theorems.Thm_GlobalTheory_RankFibreKer_tw_mul
-- name    : GlobalTheory.RankFibreKer.tw_mul
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T19:14:08.344265+00:00
-- url     : https://prove2.me/theorems/21671c0f-c269-4b6e-920c-15895708a1b2
-- title:
--   Rank Fibre Ker: tw mul
-- statement:
--   The Rank Fibre Ker construction uses the tw mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/OmAOneApply.lean#L34-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/OmAOneApply.lean#L34-L35

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FullRankSB
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_BernsteinUnitaryProductIrreducible
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_OmAOneApply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory ValuativeRel GlobalTheory.SplitFlip GlobalTheory.SmGL GlobalTheory.WeilM GlobalTheory.RankFibre GlobalTheory.SplitWeil
open GlobalTheory GlobalTheory.RankFibreKer
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem GlobalTheory.RankFibreKer.tw_mul (ν : kˣ →* ℂˣ) (d : ℕ) {a : ℕ} (g x : GL (Fin a) k) : tw ν d (g * x) = tw ν d g * tw ν d x := by sorry
