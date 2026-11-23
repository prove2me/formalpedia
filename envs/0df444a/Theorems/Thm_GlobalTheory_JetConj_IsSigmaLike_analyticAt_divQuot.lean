-- Prove2me | Theorems.Thm_GlobalTheory_JetConj_IsSigmaLike_analyticAt_divQuot
-- name    : GlobalTheory.JetConj.IsSigmaLike.analyticAt_divQuot
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:15:05.124173+00:00
-- url     : https://prove2.me/theorems/f66a818e-6a24-4d3f-bdee-0a136fcf60ca
-- title:
--   Is Sigma Like: analytic At div Quot
-- statement:
--   The Is Sigma Like construction uses the analytic At div Quot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/SecondDerivSigmaProductAtZero.lean#L116-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/SecondDerivSigmaProductAtZero.lean#L116-L121

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_WeierstrassPAddOfNeOfDerivNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_JetRelOfWeierstrassSystem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SecondDerivSigmaProductAtZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology PeriodPair
open GlobalTheory GlobalTheory.JetConj
variable {L : PeriodPair} {σ : ℂ → ℂ}

theorem GlobalTheory.JetConj.IsSigmaLike.analyticAt_divQuot (H : IsSigmaLike L σ) {u z : ℂ} (hz : z + u ∉ L.lattice) (n : ℕ) :
    AnalyticAt ℂ (divQuot σ u n) z := by sorry
