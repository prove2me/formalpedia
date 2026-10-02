-- Prove2me | Theorems.Thm_MDPFinance_TerminalWealth_hara_utility_solution
-- name    : MDPFinance.TerminalWealth.hara_utility_solution
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T21:57:31.390365+00:00
-- url     : https://prove2.me/theorems/ec84c814-1ff6-4fd5-acdc-5bf51fb42ad7
-- title:
--   Theorem 4.2.11 — HARA-utility closed form
-- statement:
--   Let $U(x)=(x+b)^\gamma$, $b\geq0$, $0<\gamma<1$, $E_n := \{x : xS^0_N/S^0_n+b\geq0\}$. Then
--   $V_n(x) = d_n(xS^0_N/S^0_n+b)^\gamma$ with $d_N=1$, $d_n=\sum_{k=n}^{N-1}v_k$; the optimal amounts
--   are $f_n^*(x) = \alpha_n^*(x+bS^0_n/S^0_N)$ for the optimal solution $\alpha_n^*$ of (4.7) — the
--   same one-period sub-problem as the power-utility case, after a wealth shift.
--
--   **Formalization Note (moderation).** $d_n = \prod_{k=n}^{N-1} v_k$: the backward recursion
--   $V_n = d_{n+1}\,v_n\,(xS^0_N/S^0_n + b)^\gamma$ multiplies the one-period values (as in the
--   power case), it does not add them.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 88, PDF 102, Theorem 4.2.11

import Mathlib
import Definitions.Def_MDPFinance_TerminalWealth_Market
import Definitions.Def_MDPFinance_TerminalWealth_PowerAuxiliary

open MeasureTheory ProbabilityTheory

namespace MDPFinance.TerminalWealth

/-- Theorem 4.2.11 (Bäuerle–Rieder, p. 88, PDF 102). Under Assumption (FM) (`hFM2`), let
`U(x) = (x+b)^γ` be the HARA utility with `b ≥ 0`, `0 < γ < 1`, `domU = [-b,∞)`. With
`E_n := {x | x·S⁰_N/S⁰_n + b ≥ 0}`: a) the value functions are `V_n(x) = d_n(x·S⁰_N/S⁰_n + b)^γ`,
`x ∈ E_n`, with `d_N = 1` and `d_n = ∏_{k=n}^{N-1} v_k` (`v_k` the value of problem (4.7)); b) the
optimal amounts invested in the stocks are `f_n^*(x) = α_n^*(x + bS⁰_n/S⁰_N)`, `x ∈ E_n`, where
`α_n^*` is the optimal solution of (4.7); the optimal portfolio strategy is
`(f_0^*,…,f_{N-1}^*)`. -/
theorem hara_utility_solution {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (M : TerminalWealthMarket Ω d) (hFM2 : M.FM2) (γ b : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hb : 0 ≤ b) (hdomU : M.domU = Set.Ici (-b))
    (hU : ∀ x, -b ≤ x → M.U x = (x + b) ^ γ)
    (En : ℕ → Set ℝ) (hEn : ∀ n, En n = {x | 0 ≤ x * M.S0 M.N / M.S0 n + b}) :
    (∀ n ≤ M.N, ∀ x ∈ En n,
        M.V n x = (((∏ k ∈ Finset.Ico n M.N, M.vPower γ k) *
          (x * M.S0 M.N / M.S0 n + b) ^ γ : ℝ) : EReal)) ∧
      (∃ αstar : ℕ → (Fin d → ℝ), (∀ n < M.N, αstar n ∈ M.Afrac n ∧
          ∫ ω, (1 + ∑ k, αstar n k * M.R (n + 1) ω k) ^ γ ∂M.measIP = M.vPower γ n) ∧
        ∃ fstar : ℕ → ℝ → (Fin d → ℝ), M.IsAdmissible 0 fstar ∧
          (∀ n < M.N, ∀ x ∈ En n,
            fstar n x = fun k => αstar n k * (x + b * M.S0 n / M.S0 M.N)) ∧
          ∀ x ∈ En 0, M.Vpi fstar 0 x = M.V 0 x) := by sorry

end MDPFinance.TerminalWealth
