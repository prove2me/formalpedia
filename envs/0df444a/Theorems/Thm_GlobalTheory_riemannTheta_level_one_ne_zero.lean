-- Prove2me | Theorems.Thm_GlobalTheory_riemannTheta_level_one_ne_zero
-- name    : GlobalTheory.riemannTheta_level_one_ne_zero
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T16:46:41.826227+00:00
-- url     : https://prove2.me/theorems/fbe4f513-62b4-5734-8076-4ed732192e59
-- title:
--   Global Theory: riemann Theta level one ne zero
-- statement:
--   The Global Theory construction uses the riemann Theta level one ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/RiemannThetaLevelOneNeZero.lean#L14-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/RiemannThetaLevelOneNeZero.lean#L14-L29

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EqZeroOfSemicharacterMultiplier
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_RiemannThetaLevelOneNeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.PTheta Complex Matrix Filter Topology
open scoped BigOperators Real
open GlobalTheory
open Complex Matrix Filter Topology
open scoped BigOperators Real

theorem GlobalTheory.riemannTheta_level_one_ne_zero :
    (∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ _root_.ReciprocityTheory.PTheta.SiegelH (Fin g) → ∀ N : ℕ, 1 ≤ N → (∀ c : Fin g → Fin N, (Differentiable ℂ (fun z => _root_.ReciprocityTheory.PTheta.theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)) ∧ ∀ (n n' : Fin g → ℤ) z, (fun z => _root_.ReciprocityTheory.PTheta.theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)) (z + τ *ᵥ _root_.ReciprocityTheory.PTheta.ofIntVec n + _root_.ReciprocityTheory.PTheta.ofIntVec n') = _root_.ReciprocityTheory.PTheta.eC (-(N : ℂ) * (_root_.ReciprocityTheory.PTheta.ofIntVec n ⬝ᵥ (τ *ᵥ _root_.ReciprocityTheory.PTheta.ofIntVec n) / 2 + _root_.ReciprocityTheory.PTheta.ofIntVec n ⬝ᵥ z)) * (fun z => _root_.ReciprocityTheory.PTheta.theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ)) z)) ∧ LinearIndependent ℂ (fun (c : Fin g → Fin N) (z : Fin g → ℂ) => _root_.ReciprocityTheory.PTheta.theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ))) → (∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ _root_.ReciprocityTheory.PTheta.SiegelH (Fin g) → (Differentiable ℂ (fun z => _root_.ReciprocityTheory.PTheta.theta 0 0 z τ) ∧ ∀ (n n' : Fin g → ℤ) z, (fun z => _root_.ReciprocityTheory.PTheta.theta 0 0 z τ) (z + τ *ᵥ _root_.ReciprocityTheory.PTheta.ofIntVec n + _root_.ReciprocityTheory.PTheta.ofIntVec n') = _root_.ReciprocityTheory.PTheta.eC (-(1 : ℂ) * (_root_.ReciprocityTheory.PTheta.ofIntVec n ⬝ᵥ (τ *ᵥ _root_.ReciprocityTheory.PTheta.ofIntVec n) / 2 + _root_.ReciprocityTheory.PTheta.ofIntVec n ⬝ᵥ z)) * (fun z => _root_.ReciprocityTheory.PTheta.theta 0 0 z τ) z) ∧ (fun z => _root_.ReciprocityTheory.PTheta.theta 0 0 z τ) ≠ 0) := by sorry
