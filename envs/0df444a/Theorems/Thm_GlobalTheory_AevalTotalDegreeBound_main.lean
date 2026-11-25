-- Prove2me | Theorems.Thm_GlobalTheory_AevalTotalDegreeBound_main
-- name    : GlobalTheory.AevalTotalDegreeBound.main
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T11:55:18.051283+00:00
-- url     : https://prove2.me/theorems/1c4c8bde-0726-44b9-842d-76179a5a6b23
-- title:
--   Aeval Total Degree Bound: main
-- statement:
--   The Aeval Total Degree Bound construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/AevalTotalDegreeLe.lean#L25-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/AevalTotalDegreeLe.lean#L25-L26

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

theorem GlobalTheory.AevalTotalDegreeBound.main : ∀ {σ : Type u_1} (f : σ → MvPolynomial σ ℂ), (∀ (v : σ), MvPolynomial.totalDegree (f v) ≤ (1 : ℕ)) → ∀ (P : MvPolynomial σ ℂ), MvPolynomial.totalDegree ((MvPolynomial.aeval f : MvPolynomial σ ℂ → MvPolynomial σ ℂ) P) ≤ MvPolynomial.totalDegree P := by sorry
