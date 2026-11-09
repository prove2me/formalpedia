-- Prove2me | Theorems.Thm_MinimaxAltRegret_Main_proposition_A_1
-- name    : MinimaxAltRegret.Main.proposition_A_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:55:36.376977+00:00
-- url     : https://prove2.me/theorems/f2071e18-aed8-4ebc-9358-7c52f1beadc5
-- title:
--   Proposition A.1 — corrected expert action is feasible
-- statement:
--   Let d,T be positive integers and let ell_1,...,ell_T belong to [-1,1]^d. For Algorithm 1 with eta=1/10, every corrected action, including the terminal action selected after observing ell_T, is a probability vector:
--
--   $$p_t\in\Delta_d\qquad(1\le t\le T+1).$$
--
--   This makes the displayed update a legal expert learner without assuming its feasibility in the definition. The parameter convention d>=1 and positive horizon is the standing convention of Section 2.
--
--   Differences from the source:
--   - encoding: rounds 1 through T and the terminal action x_(T+1) → zero-based losses and actions, with action T terminal and source score R_t stored at index t; reason: a bijective reindexing preserves every summand and includes the same terminal update
-- source:
--   Mengxiao Zhang, STOC 2027 submission #57 (October 2026), printed p. 14 / PDF p. 15, Proposition A.1; SHA-256 6db5a23e9e92d250b4dea7995bf34c9930d39a95df90f5d3fdc715ca26044f31

import Mathlib
import Definitions.Def_MinimaxAltRegret_Main_Experts

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

namespace MinimaxAltRegret.Main

theorem proposition_A_1 (d T : ℕ) (hd : 0 < d) (hT : 0 < T)
    (ℓ : ℕ → ExpertVector d) (hℓ : expertLosses d T ℓ) :
    ∀ t ≤ T, expertAlgorithm T ℓ t ∈ stdSimplex ℝ (Fin d) := by sorry

end MinimaxAltRegret.Main
