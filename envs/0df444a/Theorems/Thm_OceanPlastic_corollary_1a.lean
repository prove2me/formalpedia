-- Prove2me | Theorems.Thm_OceanPlastic_corollary_1a
-- name    : OceanPlastic.corollary_1a
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:52:35.771943+00:00
-- url     : https://prove2.me/theorems/ced7d7b5-b387-4bd4-82c0-898d427b080c
-- title:
--   Corollary 1(a) — the for-profit optimum with additionality
-- statement:
--   Let the firm be a profit maximizer ($\rho_1=1$, $\rho_2=\rho_3=0$), with $\delta_o^2kQ_o\le2M\bar v_o$ (Assumption 1(2) at these weights).
--
--   1. If $p_m\le\bar v_o$, problem (4) has the unique optimal solution
--   $$\tilde d_o=\frac{MQ_o(\bar v_o-p_m)}{2M\bar v_o+4k(1-\delta_o)Q_o},\qquad \tilde r=\frac{kQ_o(\bar v_o-p_m)}{M\bar v_o+2k(1-\delta_o)Q_o}.$$
--   2. If $\bar v_o\le p_m$, its unique optimal solution is $(\tilde r,\tilde d_o)=(0,0)$.
--   3. Every optimal solution has $E^O(\tilde r)\ge0$ and $S^O(\tilde r)\ge0$.
--
--   This is the first of the two optima compared in Proposition 5: under additionality the firm's bonus falls with the local price and vanishes at $p_m=\bar v_o$.
--
--   Differences from the source:
--   - generalization: "the firm enters the local market as long as p_m ≤ v̄_o", with closed forms for that range → adds the clause: for v̄_o ≤ p_m the unique optimum is (0, 0); reason: makes the entry statement precise; on p_m ≤ v̄_o the statement is the printed one
--   - reading: "the equilibrium outcomes are" → (r, d) optimal for (4) ↔ (r, d) is the printed pair; reason: the equilibrium is the optimal solution of the firm's problem, which the paper treats as unique
--   - encoding: Assumption 1(2) at ρ_1 = 1, ρ_2 = ρ_3 = 0: δ_o ≤ √(2Mv̄_o/(kQ_o)) → δ_o² k Q_o ≤ 2 M v̄_o; reason: equivalent since δ_o ≥ 0; (1) is 1 > 0 and (3) concerns Case S only
--   - reading: M, v̄_o, Q_o unspecified positive sizes; p_m a price; c_E^r with no stated sign → real M, v̄_o, Q_o > 0, p_m ≥ 0, c_E^r ≥ 0 (fields of Params), with k > 0, δ_o ∈ [0,1), ρ_p ∈ (0,1] as printed; reason: sizes, a price and a value; v̄_o is the upper end of a uniform law; M is real as in the paper, which differentiates in M
-- source:
--   Baron–Romero–Zhang–Zhou, Innovative Business Models in Ocean-Bound Plastic Recycling, MSOM, doi:10.1287/msom.2022.0643, Corollary 1(a), p.18

import Mathlib
import Definitions.Def_OceanPlastic_Params
import Definitions.Def_OceanPlastic_Benchmark
import Definitions.Def_OceanPlastic_CaseO
import Definitions.Def_OceanPlastic_Problem4

namespace OceanPlastic

open Params

/-- **Corollary 1(a): the for-profit optimum with additionality.** Baron–Romero–Zhang–Zhou, MSOM,
doi:10.1287/msom.2022.0643, Corollary 1(a), p. 18.

Take the for-profit weights `ρ₁ = 1`, `ρ₂ = ρ₃ = 0` and Assumption 1(2) at these weights,
`δ_o² k Q_o ≤ 2 M v̄_o`. If `p_m ≤ v̄_o`, the unique optimal solution of (4) is
`d̃_o = M Q_o (v̄_o − p_m) / (2 M v̄_o + 4 k (1 − δ_o) Q_o)`,
`r̃ = k Q_o (v̄_o − p_m) / (M v̄_o + 2 k (1 − δ_o) Q_o)`. If `v̄_o ≤ p_m`, the unique optimal solution
is `(0, 0)`. Every optimal solution has `E^O ≥ 0` and `S^O ≥ 0`.

**Formalization Note** The clause for `v̄_o ≤ p_m` is an addition that makes precise "the firm enters
the local market as long as `p_m ≤ v̄_o`". The denominators are positive for every `P : Params`. -/
theorem corollary_1a (P : Params) (hA : P.δ ^ 2 * P.k * P.Q ≤ 2 * P.M * P.vbar) :
    (P.pm ≤ P.vbar → ∀ r d : ℝ, P.IsOptimal 1 0 0 r d ↔
      d = P.M * P.Q * (P.vbar - P.pm) / (2 * P.M * P.vbar + 4 * P.k * (1 - P.δ) * P.Q) ∧
      r = P.k * P.Q * (P.vbar - P.pm) / (P.M * P.vbar + 2 * P.k * (1 - P.δ) * P.Q)) ∧
    (P.vbar ≤ P.pm → ∀ r d : ℝ, P.IsOptimal 1 0 0 r d ↔ d = 0 ∧ r = 0) ∧
    (∀ r d : ℝ, P.IsOptimal 1 0 0 r d → P.EO r ≥ 0 ∧ P.SO r ≥ 0) := by sorry

end OceanPlastic
