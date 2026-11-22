-- Prove2me | Theorems.Thm_Lean4LPD_cZero_le_two_without_m_le_r
-- name    : Lean4LPD.cZero_le_two_without_m_le_r
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:03:43.168802+00:00
-- url     : https://prove2.me/theorems/59be8a10-20bb-4b83-b91d-85a5d963bccc
-- title:
--   Lean4 LPD: c Zero le two without m le r
-- statement:
--   **`c₀ ≤ 2` does not need `Admissible`'s clause `m ≤ r`.** The hypotheses here are
--   `8(m*+1)² ≤ rΓ`, `1 ≤ m`, `5 ≤ r` and `0 ≤ B ≤ 1`, and this set is strictly weaker than that of
--   `cZero_le_two`, not a restatement of it: `(r, m*, Γ) = (5, 100, 20000)` satisfies every hypothesis
--   below and violates `m ≤ r`.
--
--   **Nor does it need `0 < Γ`**, which is *derivable*: `8(m*+1)² ≤ rΓ` with `m* ≥ 1` gives
--   `rΓ ≥ 32 > 0`, and `r ≥ 5 > 0`. So of `Admissible`'s five clauses only `8(m*+1)² ≤ rΓ` remains as
--   a hypothesis; `1 ≤ r` and `0 ≤ m` are subsumed by `5 ≤ r` and `1 ≤ m`, and the other two are
--   unnecessary.
--
--   The argument is that of `cZero_le_two_sharp`, which never uses `m ≤ r`: it destructures
--   `Admissible` and passes the clause on to `exp_factor_le`, which discards it.
--
--   Scope: this statement concerns the constant `c₀` only. It does not show that the condition
--   `r ≥ m*` is dispensable elsewhere in the analysis, for instance in the multi-jump majorant
--   `apd:eq:composition_majorant`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Constants/C0.lean#L223-L250
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Constants/C0.lean#L223-L250

module
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_C0
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Real

theorem Lean4LPD.cZero_le_two_without_m_le_r {r m G B : ℝ}
    (hrG : 8 * (m + 1) ^ 2 ≤ r * G) (hm1 : 1 ≤ m) (hr5 : 5 ≤ r) (hB0 : 0 ≤ B) (hB1 : B ≤ 1) :
    cZero r m G B ≤ 2 := by sorry
