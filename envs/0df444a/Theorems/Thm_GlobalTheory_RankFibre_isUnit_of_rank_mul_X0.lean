-- Prove2me | Theorems.Thm_GlobalTheory_RankFibre_isUnit_of_rank_mul_X0
-- name    : GlobalTheory.RankFibre.isUnit_of_rank_mul_X0
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T22:31:32.581527+00:00
-- url     : https://prove2.me/theorems/441e6b8d-6629-4105-81ac-0b3c82786df5
-- title:
--   Rank Fibre: is Unit of rank mul X0
-- statement:
--   The Rank Fibre construction uses the is Unit of rank mul X0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IntegrableFullRankFibre.lean#L17-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IntegrableFullRankFibre.lean#L17-L25

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

theorem GlobalTheory.RankFibre.isUnit_of_rank_mul_X0 {k : Type} [Field k] {a b : ℕ} (A : Matrix (Fin a) (Fin a) k)
    (h : (A * GlobalTheory.SplitFlip.X0 k (finSumFinEquiv (m := a) (n := b))).rank = a) : IsUnit A := by sorry
