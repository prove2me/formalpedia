-- Prove2me | Theorems.Thm_GlobalTheory_AevalTotalDegreeBound_aeval_totalDegree_le
-- name    : GlobalTheory.AevalTotalDegreeBound.aeval_totalDegree_le
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:01:22.340029+00:00
-- url     : https://prove2.me/theorems/a077916e-fe4c-4848-89bd-3be2d64f3129
-- title:
--   Aeval Total Degree Bound: aeval total Degree le
-- statement:
--   The Aeval Total Degree Bound construction uses the aeval total Degree le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/AevalTotalDegreeLe.lean#L6-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/AevalTotalDegreeLe.lean#L6-L23

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_AevalTotalDegreeLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1
open GlobalTheory GlobalTheory.AevalTotalDegreeBound
open MvPolynomial

theorem GlobalTheory.AevalTotalDegreeBound.aeval_totalDegree_le {σ : Type u_1} (f : σ → MvPolynomial σ ℂ)
    (hf : ∀ v, (f v).totalDegree ≤ 1) (P : MvPolynomial σ ℂ) :
    (aeval f P).totalDegree ≤ P.totalDegree := by sorry
