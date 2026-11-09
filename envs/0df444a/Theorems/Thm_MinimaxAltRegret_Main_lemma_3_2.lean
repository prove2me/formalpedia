-- Prove2me | Theorems.Thm_MinimaxAltRegret_Main_lemma_3_2
-- name    : MinimaxAltRegret.Main.lemma_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:55:39.212798+00:00
-- url     : https://prove2.me/theorems/a714a954-ce99-440d-afce-befc4135ece7
-- title:
--   Lemma 3.2 — concavity and the pre-update distribution
-- statement:
--   Let d>=1 and let R,ell,z be d-vectors with ell,ell-z in [-1,1]^d. At eta=1/10, set G_2(theta)=U_2(R-theta z,ell-theta z), and let p be the corrected distribution (4) computed from the known state (R,ell). Then
--
--   $$G_2\text{ is concave on }[0,1],\qquad G'_2(0)=-\langle p,z\rangle.$$
--
--   The statement also records p in Delta_d and measurability of the map from the known state (R,ell) to p. Therefore a measurable pre-update state produces the source's pre-update measurable action. The derivative is the ordinary derivative of the displayed smooth extension.
--
--   This is the potential criterion used for Theorem 3.3, retaining both clauses rather than only the curvature sign.
--
--   Differences from the source:
--   - generalization: p_t is a pre-update measurable distribution on the stated bounded-loss states → p is a simplex vector on every bounded-loss state and the correction map is globally measurable on all real score and previous-loss pairs; reason: the explicit exponential and polynomial formula extends smoothly to arbitrary real state pairs; restricting to the source states gives the exact pre-update measurable distribution, without enlarging its feasible-state claim
-- source:
--   Mengxiao Zhang, STOC 2027 submission #57 (October 2026), printed p. 8 / PDF p. 9, Lemma 3.2; SHA-256 6db5a23e9e92d250b4dea7995bf34c9930d39a95df90f5d3fdc715ca26044f31

import Mathlib
import Definitions.Def_MinimaxAltRegret_Main_Experts

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

namespace MinimaxAltRegret.Main

theorem lemma_3_2 (d : ℕ) (hd : 0 < d) (R ℓ z : ExpertVector d)
    (hℓ : ∀ i, ℓ i ∈ Set.Icc (-1 : ℝ) 1)
    (hend : ∀ i, ℓ i - z i ∈ Set.Icc (-1 : ℝ) 1) :
    ConcaveOn ℝ (Set.Icc (0 : ℝ) 1) (expertG 2 (1/10) R ℓ z) ∧
    HasDerivAt (expertG 2 (1/10) R ℓ z)
      (-expertDot (expertCorrection (1/10) R ℓ) z) 0 ∧
    expertCorrection (1/10) R ℓ ∈ stdSimplex ℝ (Fin d) ∧
    Measurable (fun state : ExpertVector d × ExpertVector d =>
      expertCorrection (1/10) state.1 state.2) := by sorry

end MinimaxAltRegret.Main
