-- Prove2me | Theorems.Thm_GlobalTheory_exists_entire_dirichlet_of_theta
-- name    : GlobalTheory.exists_entire_dirichlet_of_theta
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T22:31:53.543324+00:00
-- url     : https://prove2.me/theorems/340ff452-1eda-4b75-b6a0-4b3271dc1cd5
-- title:
--   Global Theory: exists entire dirichlet of theta
-- statement:
--   The Global Theory construction uses the exists entire dirichlet of theta property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/LatticeEpsteinZetaContinuation.lean#L84-L164
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/LatticeEpsteinZetaContinuation.lean#L84-L164

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_NonemptyRayDataOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_LatticeThetaAsymptoticsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_LatticeEpsteinZetaContinuation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Asymptotics
open GlobalTheory
open Set MeasureTheory
open scoped Topology

theorem GlobalTheory.exists_entire_dirichlet_of_theta {ι : Type*} [Countable ι] {q : ι → ℝ}
    (hq : ∀ i, 0 < q i) (hs : ∀ σ : ℝ, 1 < σ → Summable fun i => q i ^ (-σ)) {V c : ℝ}
    (hc : 0 < c)
    (htop : (fun t : ℝ => ∑' i, Real.exp (-Real.pi * t * q i)) =O[atTop]
      (fun t => Real.exp (-c * t)))
    (hbot : (fun t : ℝ => (∑' i, Real.exp (-Real.pi * t * q i)) - 1 / (t * V)) =O[𝓝[>] 0]
      (fun t => Real.exp (-c / t))) :
    ∃ Z : ℂ → ℂ, Differentiable ℂ Z ∧ Z 1 = (Real.pi / V : ℝ) ∧ Z (-1) = 0 ∧
      ∀ s : ℂ, 1 < s.re → Summable (fun i => ((q i : ℝ) : ℂ) ^ (-s)) ∧
        Z s = (s - 1) * ∑' i, ((q i : ℝ) : ℂ) ^ (-s) := by sorry
