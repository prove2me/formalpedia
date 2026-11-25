-- Prove2me | Theorems.Thm_GlobalTheory_RankFibre_fibre_omA
-- name    : GlobalTheory.RankFibre.fibre_omA
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:19:43.469511+00:00
-- url     : https://prove2.me/theorems/6828782c-adb5-509c-9c96-da0208ec8560
-- title:
--   Rank Fibre: fibre om A
-- statement:
--   The Rank Fibre construction uses the fibre om A property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FullRankSB.lean#L43-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FullRankSB.lean#L43-L48

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FullRankSB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory GlobalTheory.SplitFlip GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.WeilM
open GlobalTheory GlobalTheory.RankFibre
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable [MeasurableSpace k] [BorelSpace k]

theorem GlobalTheory.RankFibre.fibre_omA (ν β : kˣ →* ℂˣ) (a b : ℕ) (h : GL (Fin (a + b)) k) (Φ : Matrix (Fin a) (Fin (a + b)) k → ℂ)
    (x : GL (Fin (a + b)) k) : fibre ν β a b (omA ν β 1 h Φ) x = fibre ν β a b Φ (x * h) := by sorry
