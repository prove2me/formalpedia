-- Prove2me | Theorems.Thm_Lean4LPD_total_truncation_error
-- name    : Lean4LPD.total_truncation_error
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:02:03.142813+00:00
-- url     : https://prove2.me/theorems/3009312f-759e-4ec6-89e1-368656928071
-- title:
--   Lean4 LPD: total truncation error
-- statement:
--   **The summed truncation error, with a threshold free of `c₀`.**
--
--   Given the summed bound in the `c₀` form of `apd:eq:total_high_weight_norm` (`hstep`, the
--   hypothesis discussed in the module docstring), the bound may be restated with `t₀` taken from
--   model parameters:
--
--     `S ≤ (t/t₀)^{m*+1} · (∏_{i=1}^{m*+1}(i+c)) / (m*+1)! · ‖O‖`,   `t₀ = 1/(2Γ(k_h−1)α)`.
--
--   Two things happen in the algebra and both matter. `c₀ ≤ 2` (`Lean4LPD.cZero_le_two`, whence the
--   hypotheses `hm1`, `hr5`, `hB0`, `hB1`) replaces the parameter-dependent constant by a literal,
--   and then the `(k_h−1)^{m*+1}` produced by `prod_rungW_eq` is **absorbed exactly** into the decay
--   base: since `1/t₀ = 2Γ(k_h−1)α`, one has `(2Γαt)^{m*+1} · (k_h−1)^{m*+1} = (t/t₀)^{m*+1}`. So
--   besides offsetting the factorial `(m*+1)!` (compare `apd:rmk:comparison`), the rung product is
--   what supplies the factor `k_h − 1` of the threshold.
--
--   The conclusion is the norm-level content of `apd:eq:total_truncation_error` *before* the product
--   `∏_{i=1}^{m*+1}(i+c)` is estimated. That estimate, `∏_{i=1}^{n}(i+c) ≤ n!·(e·n)^c`, is
--   `prod_add_one_le_factorial_exp_rpow`; `total_truncation_error_product_bound` composes the two and
--   is the version downstream code uses. The statement is about real numbers `S` and `M`, standing
--   for the summed high-weight norm and `‖O‖`; no conversion to an error in expectation is made
--   here.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Constants/Total.lean#L178-L238
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Constants/Total.lean#L178-L238

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_C0
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_StepSum
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_Total
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Finset

theorem Lean4LPD.total_truncation_error {S M t a G kh1 c B : ℝ} {m r : ℕ}
    (hstep : S ≤ (cZero (r : ℝ) (m : ℝ) G B * G * a * t) ^ (m + 1)
              * (∏ j ∈ range (m + 1), rungW kh1 c (j + 2))
              / (Nat.factorial (m + 1) : ℝ) * M)
    (hadm : Admissible (r : ℝ) (m : ℝ) G) (hm1 : 1 ≤ (m : ℝ)) (hr5 : 5 ≤ (r : ℝ))
    (hB0 : 0 ≤ B) (hB1 : B ≤ 1) (hkh1 : 0 < kh1) (hc : 0 ≤ c)
    (ha : 0 < a) (ht : 0 ≤ t) (hM : 0 ≤ M) :
    S ≤ decayBase G (kh1 + 1) a t ^ (m + 1)
          * (∏ i ∈ range (m + 1), ((i : ℝ) + 1 + c))
          / (Nat.factorial (m + 1) : ℝ) * M := by sorry
