-- Prove2me | Theorems.Thm_MDPFinance_MeanVariance_mutual_fund_theorem
-- name    : MDPFinance.MeanVariance.mutual_fund_theorem
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-27T22:08:27.986284+00:00
-- url     : https://prove2.me/theorems/2b0d7528-88fd-4e0a-816f-4c2dbf8d64a2
-- title:
--   Corollary 4.6.7 (Two-Fund Theorem) — the optimal policy holds one mutual fund
-- statement:
--   At any time, the optimal policy of Theorem 4.6.6 invests a certain amount of money in
--   the bond, and the remaining money along a *fixed* direction
--   $C_{n+1}^{-1}\mathbb{E}[R_{n+1}] \in\mathbb{R}^d$ (the "mutual fund") independent of the
--   current wealth $x$: only the scalar amount invested in this fund depends on $x$ and $n$.
--
--   This is the multistage analogue of the classical (static) Markowitz Two-Fund Theorem: every
--   investor, regardless of wealth or target return, holds the *same* portfolio of risky assets
--   (up to a scalar), differing only in how much of it they hold versus the riskless bond.
--
--   **Formalization Note.** Stated as: given the optimal policy's explicit form from Theorem 4.6.6,
--   there is a fund direction `mutualFund n` (depending only on $n$, not on $x$) and a scalar $s$
--   (depending on both) with $\pi_n^*(x) = s\cdot\text{mutualFund}(n)$ — directly reading off the
--   factorization already present in Theorem 4.6.6's formula, exactly as the book's one-line proof
--   does.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 124, PDF 138, Corollary 4.6.7

import Mathlib
import Definitions.Def_MDPFinance_MeanVariance_MVMarket
import Definitions.Def_MDPFinance_MeanVariance_MVAuxiliary

open MeasureTheory ProbabilityTheory

namespace MDPFinance.MeanVariance

/-- Corollary 4.6.7 (Two-Fund Theorem) (Bäuerle–Rieder, p. 124, PDF 138). In the representation
of the optimal policy `π^*` of Theorem 4.6.6, the first factor is a real number and
`C_{n+1}^{-1}𝔼[R_{n+1}]` is a fixed vector (the "mutual fund"): at any time `n`, the optimal
policy invests a scalar amount `s_n(x)` of money along this fixed direction, i.e. the remaining
money (after the bond) is invested in a single mutual fund independent of `x`. -/
theorem mutual_fund_theorem {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (M : MVMarket Ω d)
    (dseq : ℕ → ℝ) (hdN : dseq M.N = 1)
    (hdrec : ∀ n < M.N, dseq n = dseq (n + 1) * (1 - M.ell (n + 1)))
    (πstar : ℕ → ℝ → (Fin d → ℝ))
    (hπstar : ∀ n < M.N, ∀ x : ℝ, πstar n x =
      fun k => ((M.μ - dseq 0 * M.x0 * M.S0 M.N) / (1 - dseq 0) * (M.S0 n / M.S0 M.N) - x) *
        ((M.Cmat (n + 1))⁻¹.mulVec (M.Evec (n + 1)) k)) :
    ∃ mutualFund : ℕ → (Fin d → ℝ), ∀ n < M.N, ∀ x : ℝ,
      ∃ s : ℝ, πstar n x = fun k => s * mutualFund n k := by sorry

end MDPFinance.MeanVariance
