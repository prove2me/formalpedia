-- Prove2me | Theorems.Thm_GlobalTheory_RankFibre_X0_mul_X0_transpose
-- name    : GlobalTheory.RankFibre.X0_mul_X0_transpose
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T22:31:11.227788+00:00
-- url     : https://prove2.me/theorems/72c4d83f-eb9f-460e-8a7c-dbeae3dbec5f
-- title:
--   Rank Fibre: X0 mul X0 transpose
-- statement:
--   The Rank Fibre construction uses the X0 mul X0 transpose property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IntegrableFullRankFibre.lean#L11-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IntegrableFullRankFibre.lean#L11-L15

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FullRankSB
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_BernsteinUnitaryProductIrreducible
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ThetaIntegralIntegrable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormalizedAbsCharacterization
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegrableFullRankFibre
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix Topology
open GlobalTheory GlobalTheory.RankFibre

theorem GlobalTheory.RankFibre.X0_mul_X0_transpose (k : Type) [Field k] (a b : ℕ) :
    GlobalTheory.SplitFlip.X0 k (finSumFinEquiv (m := a) (n := b)) * (GlobalTheory.SplitFlip.X0 k (finSumFinEquiv (m := a) (n := b)))ᵀ = 1 := by sorry
