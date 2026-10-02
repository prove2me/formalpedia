-- Prove2me | Theorems.Thm_MDPFinance_IndifferencePricing_multiperiod_indifference_solution
-- name    : MDPFinance.IndifferencePricing.multiperiod_indifference_solution
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T22:10:40.188811+00:00
-- url     : https://prove2.me/theorems/31a07730-e0f4-4330-826a-de4086bc8605
-- title:
--   Theorem 4.9.4 — multiperiod indifference price via an explicit recursion [GOAL]
-- statement:
--   a) $V_n^H(x,s,\hat s) = -e^{-\gamma x}d_n(s,\hat s)$ where $(d_n)$ satisfies
--   $d_N(s,\hat s):=e^{\gamma h(s,\hat s)}$,
--   $$d_n(s,\hat s) := \inf_{a\in\mathbb{R}} \mathbb{E}\big[e^{-\gamma a(\tilde
--   R_{n+1}-1)}\,d_{n+1}(s\tilde R_{n+1},\hat s\hat R_{n+1})\big];$$
--   in particular $V_n^0(x,s,\hat s) = -e^{-\gamma x}v^{N-n}$. b) The indifference price is
--   $v_n(H,s,\hat s) = \frac{1}{\gamma}\log\big(d_n(s,\hat s)/v^{N-n}\big)$.
--   c) The indifference prices satisfy the consistency condition
--   $v_n\big(v_{n+1}(H,s\tilde R_{n+1},\hat s\hat R_{n+1}),s,\hat s\big) = v_n(H,s,\hat s)$:
--   pricing at time $n$ a claim whose payoff at $n+1$ is itself the time-$(n+1)$ indifference price
--   of $H$ gives back $H$'s own time-$n$ price.
--
--   This is the goal of the mission: the genuine multiperiod dynamic-programming solution of
--   indifference pricing, of which Theorem 4.9.2 is the $N=1$ special case, obtained by folding the
--   contingent claim's payoff into the terminal reward of the exponential-utility Bellman recursion
--   of Theorem 4.2.15 and reading off $V_n^H$ as an explicit multiplicative recursion in $d_n$, no
--   closed form being available in general (unlike the one-period case).
--
--   **Formalization Note.** Part c)'s consistency condition needs the value function generalized to
--   an arbitrary maturity $m$ (`VHAt`/`IsIndifferencePriceAt`, not fixed at $N$), since its left-hand
--   side prices, at time $n$, a claim maturing at $n+1$ rather than at the model's own horizon $N$;
--   this generalization is additive infrastructure, not a restatement of the book's own (single
--   maturity $N$) notation. `d_n` is named `dseq` in the Lean, distinct from every other chunk's own
--   `(d_n)`-named sequence in this book (chunk pitfall shared with `04c`'s `MRcdSeq`).
--
--   **Moderation note.** The claim $H$ is nonnegative and all state claims are on $E=\mathbb{R}\times\mathbb{R}_{>0}^2$, as in the book. Part c) is stated as: whenever $v_{n+1}(H,\cdot,\cdot)$ is a time-$(n+1)$ indifference-price function of $H$ on $\mathbb{R}_{>0}^2$, the one-period claim $v_{n+1}(H,S_{n+1},\hat S_{n+1})$ maturing at $n+1$ has a time-$n$ indifference price which is also a time-$n$ indifference price of $H$. Indifference prices are unique ($V_n^0$ is strictly increasing in $x$), so this is the book's $w_n=v_n$; the draft's implication form asserted no existence of $w_n$.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 139, PDF 153, Theorem 4.9.4

import Mathlib
import Definitions.Def_MDPFinance_IndifferencePricing_MultiperiodMarket

open MeasureTheory ProbabilityTheory

namespace MDPFinance.IndifferencePricing

/-- Theorem 4.9.4 (Bäuerle–Rieder, p. 139, PDF 153) — the goal of this mission. For the
multiperiod financial market it holds: a) `V_n^H(x,s,ŝ) = -e^{-γx}d_n(s,ŝ)` where `(d_n)`
satisfies `d_N(s,ŝ) := e^{γh(s,ŝ)}`, `d_n(s,ŝ) := inf_a 𝔼[e^{-γa(R̃_{n+1}-1)}d_{n+1}(sR̃_{n+1},
ŝR̂_{n+1})]`; in particular `V_n^0(x,s,ŝ) = -e^{-γx}v^{N-n}`. b) The indifference price of `H` is
`v_n(H,s,ŝ) = (1/γ)log(d_n(s,ŝ)/v^{N-n})`. c) The indifference prices satisfy the consistency
condition `v_n(v_{n+1}(H,sR̃_{n+1},ŝR̂_{n+1}),s,ŝ) = v_n(H,s,ŝ)`. All state claims are on the
state space `E = ℝ × ℝ_{>0} × ℝ_{>0}`; the claim `H = h(S_N,Ŝ_N)` is nonnegative (p. 134-135).
Part c) is stated as: whenever `v_{n+1}(H,·,·)` is a time-`(n+1)` indifference-price function of
`H` on `ℝ_{>0}²`, the one-period claim `v_{n+1}(H,S_{n+1},Ŝ_{n+1})` maturing at `n+1` has a
time-`n` indifference price which is also a time-`n` indifference price of `H` (indifference
prices are unique because `V_n^0` is strictly increasing in `x`, so this is the book's equation
`w_n = v_n`). -/
theorem multiperiod_indifference_solution {Ω : Type*} [MeasurableSpace Ω]
    (M : MultiperiodIndifferenceMarket Ω) (h : ℝ → ℝ → ℝ) (hh : ∀ s ŝ, 0 ≤ h s ŝ) :
    ∃ dseq : ℕ → ℝ → ℝ → ℝ,
      (∀ s ŝ, dseq M.N s ŝ = Real.exp (M.γ * h s ŝ)) ∧
      (∀ n < M.N, ∀ s ŝ,
        dseq n s ŝ = ⨅ a : ℝ, ∫ ω, Real.exp (-M.γ * a * (M.Rtilde (n + 1) ω - 1)) *
          dseq (n + 1) (s * M.Rtilde (n + 1) ω) (ŝ * M.Rhat (n + 1) ω) ∂M.measIP) ∧
      (∀ n ≤ M.N, ∀ x s ŝ, 0 < s → 0 < ŝ →
        M.VH h n x s ŝ = -Real.exp (-M.γ * x) * dseq n s ŝ) ∧
      (∀ n ≤ M.N, ∀ x s ŝ, 0 < s → 0 < ŝ →
        M.VH (fun _ _ => 0) n x s ŝ = -Real.exp (-M.γ * x) * M.vGeneric ^ (M.N - n)) ∧
      (∀ n ≤ M.N, ∀ s ŝ, 0 < s → 0 < ŝ →
        M.IsIndifferencePriceAt h M.N n s ŝ
          (1 / M.γ * Real.log (dseq n s ŝ / M.vGeneric ^ (M.N - n)))) ∧
      (∀ n < M.N, ∀ s ŝ, 0 < s → 0 < ŝ → ∀ vnext : ℝ → ℝ → ℝ,
        (∀ s' ŝ', 0 < s' → 0 < ŝ' → M.IsIndifferencePriceAt h M.N (n + 1) s' ŝ' (vnext s' ŝ')) →
        ∃ w : ℝ, M.IsIndifferencePriceAt vnext (n + 1) n s ŝ w ∧
          M.IsIndifferencePriceAt h M.N n s ŝ w) := by sorry

end MDPFinance.IndifferencePricing
