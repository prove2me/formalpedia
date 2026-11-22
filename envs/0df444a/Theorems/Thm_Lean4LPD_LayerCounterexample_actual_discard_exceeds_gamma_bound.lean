-- Prove2me | Theorems.Thm_Lean4LPD_LayerCounterexample_actual_discard_exceeds_gamma_bound
-- name    : Lean4LPD.LayerCounterexample.actual_discard_exceeds_gamma_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:47:43.567713+00:00
-- url     : https://prove2.me/theorems/cdeebd45-d29a-43f0-a9d1-97e6f49bfe91
-- title:
--   Layer Counterexample: actual discard exceeds gamma bound
-- statement:
--   **The exponent `ΥΓ` cannot be replaced by `Γ`.** For every `0<θ<π/2`, the two-local
--   disjoint-support layers `L₁`, `L₂` of `LayerWitness` (so `k_h = 2`, `Γ = 2`) produce, after one
--   second-order step from the weight-one input `Z₃`, a discarded operator `X₁` at cutoff `w* = 1`
--   (`apd:eq:step_component`) with a nonzero coefficient at a Pauli class of weight greater than
--   `w* k_h^Γ = 1 * 2 ^ 2 = 4`; the witness is `cls P₆`, of weight `6`. The weight bound
--   `w* k_h^{ΥΓ}` of `apd:thm:lightcone`, which for the `ΥΓ = 4` layers of this step equals `16`,
--   is compatible with this witness.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerCounterexample.lean#L592-L597
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerCounterexample.lean#L592-L597

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_LayerFlow
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Discard
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_LayerCounterexample
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD Lean4LPD.LayerCounterexample
open PauliString LayerWitness Finset
attribute [local irreducible] layerAct

theorem Lean4LPD.LayerCounterexample.actual_discard_exceeds_gamma_bound {θ : ℝ} (hθ : 0 < θ) (hθπ : 2 * θ < Real.pi) :
    ∃ p : PauliIndex 8, coeff (pf2Discard θ) p ≠ 0 ∧ (1 * 2 ^ 2 : ℕ) < wt p := by sorry
