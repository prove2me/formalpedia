-- Prove2me | Theorems.Thm_GlobalTheory_JetConj_IsSigmaLike_divQuot_rec
-- name    : GlobalTheory.JetConj.IsSigmaLike.divQuot_rec
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T17:39:50.187187+00:00
-- url     : https://prove2.me/theorems/d439d3c2-802e-4677-90c3-94ac42a61260
-- title:
--   Is Sigma Like: div Quot rec
-- statement:
--   The Is Sigma Like construction uses the div Quot rec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/SecondDerivSigmaProductAtZero.lean#L127-L153
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/SecondDerivSigmaProductAtZero.lean#L127-L153

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

theorem GlobalTheory.JetConj.IsSigmaLike.divQuot_rec (H : IsSigmaLike L σ) {u z : ℂ} (hz : z + u ∉ L.lattice) (n : ℕ) :
    divQuot σ u (n + 2) z * (((n + 1 : ℕ) : ℂ) ^ 2 * divQuot σ u n z) = wr (divQuot σ u (n + 1)) z := by sorry
