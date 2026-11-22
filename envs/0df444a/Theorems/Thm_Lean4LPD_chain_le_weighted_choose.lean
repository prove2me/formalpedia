-- Prove2me | Theorems.Thm_Lean4LPD_chain_le_weighted_choose
-- name    : Lean4LPD.chain_le_weighted_choose
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T06:59:16.377834+00:00
-- url     : https://prove2.me/theorems/57fa836b-0b34-4b51-83f1-e349cd69086e
-- title:
--   Lean4 LPD: chain le weighted choose
-- statement:
--   The composition-count part of `apd:eq:total_high_weight_norm`:
--
--     `chain ε E (k+1) m ≤ C · R^{m-(k+1)} · W m · C(m-1, k)`.
--
--   Local jump ratios cost at most `R^(j-1)`, while the entry estimate carries `C` exactly once;
--   summing the recursively defined chains gives the binomial count, rather than assuming that count.
--   The weight function `W` and its local ratio estimates remain explicit model inputs.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Ladder/ChainBound.lean#L203-L254
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Ladder/ChainBound.lean#L203-L254

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_StepSum
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Ladder_MultiJump
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Ladder_HockeyStick
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Ladder_ChainBound
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Finset

theorem Lean4LPD.chain_le_weighted_choose {eps : ℕ → ℕ → ℝ} {E W : ℕ → ℝ} {C R : ℝ}
    (heps : ∀ j m, 0 ≤ eps j m) (hC : 0 ≤ C) (hR : 0 ≤ R)
    (hentry : ∀ m, 1 ≤ m → E m ≤ C * R ^ (m - 1) * W m)
    (hjump : ∀ j m, 1 ≤ j → j < m →
      eps j m * W (m - j) ≤ R ^ (j - 1) * W m) :
    ∀ k m, 1 ≤ m → chain eps E (k + 1) m ≤
      C * R ^ (m - (k + 1)) * W m * ((m - 1).choose k : ℝ) := by sorry
