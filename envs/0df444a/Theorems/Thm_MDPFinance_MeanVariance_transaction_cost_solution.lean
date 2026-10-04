-- Prove2me | Theorems.Thm_MDPFinance_MeanVariance_transaction_cost_solution
-- name    : MDPFinance.MeanVariance.transaction_cost_solution
-- status  : Disproved
-- author  : @Shuze Chen
-- created : 2026-09-27T22:08:26.234252+00:00
-- url     : https://prove2.me/theorems/94a28fc5-1913-454e-a175-06c84e30a9b2
-- title:
--   Theorem 4.5.4 — explicit solution of the transaction-cost terminal-wealth problem
-- statement:
--   a) The value functions $V_n$ lie in $\mathbb{M}$ (concave, increasing, homogeneous of
--   degree $\gamma$) with $V_N(x_0,x_1) = U(x_0+x_1)$ and the Bellman recursion
--   $$V_n(x_0,x_1) = \sup_{0\le a\le x_1+x_0/(1+c)} \mathbb{E}\big[V_{n+1}\big(h(x_0,x_1,a)(1+i_{n+1}),\,
--   a\,\tilde R_{n+1}\big)\big].$$
--   b) The optimal post-transaction stock holding is the explicit three-region rule (Eq. (4.32))
--   $$f_n^*(x_0,x_1) = \begin{cases}
--   \dfrac{x_0+(1-c)x_1}{1+(1-c)q^+(V_{n+1})}\,q^+(V_{n+1}) & x_1/x_0 > q^+(V_{n+1}) \\[4pt]
--   x_1 & q^-(V_{n+1})\le x_1/x_0\le q^+(V_{n+1}) \\[4pt]
--   \dfrac{x_0+(1+c)x_1}{1+(1+c)q^-(V_{n+1})}\,q^-(V_{n+1}) & x_1/x_0 < q^-(V_{n+1})
--   \end{cases}$$
--   with optimal bond holding $h(x_0,x_1,f_n^*(x_0,x_1))$, where $q^-(V_{n+1}),q^+(V_{n+1})$ are the
--   sell/buy thresholds of Proposition 4.5.2's maximizer for the value function $V_{n+1}$.
--
--   This is the section's capstone: Proposition 4.5.2 guarantees a buy/hold/sell maximizer exists at
--   every step; Theorem 4.5.4 makes its two thresholds explicit as the argmax of the one-period
--   problems at states $(0,1)$ and $(1,0)$.
--
--   **Formalization Note.** The thresholds $q^+(V_{n+1}),q^-(V_{n+1})$ are existentially quantified via
--   their defining maximizing property (the argmax of the boundary one-period problems at $(0,1)$ and
--   $(1,0)$ respectively, transformed as in the book's proof) rather than by an explicit closed form,
--   since the book itself only pins them down as argmax's, not by a formula.
--
--   **Formalization Note (moderation).** The thresholds $q^\pm(V_{n+1})$ of (4.30)/(4.31) may be
--   $+\infty$ (never sell / never buy, (4.28)/(4.29)); a real-valued maximizer characterization
--   would be unsatisfiable in that case. They are therefore given through the largest maximizers
--   $a^+_n\in[0,1]$, $a^-_n\in[0,1/(1+c)]$ of the equivalent one-period problems at $(0,1)$ and
--   $(1,0)$ (the book's transformation $q = a/((1-c)(1-a))$), with $q^\pm=\infty$ when
--   $a^+=1$ or $a^-=1/(1+c)$, and $f_n^*$ is written on the sell/buy regions as
--   $(x_1+x_0/(1-c))a^+_n$ and $(x_0+(1+c)x_1)a^-_n$, the book's own equal forms of (4.32).
--   Statements are on $E$.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 113, PDF 127, Theorem 4.5.4

import Mathlib
import Definitions.Def_MDPFinance_MeanVariance_TransactionCostMarket
import Definitions.Def_MDPFinance_MeanVariance_TransactionCostOperators
import Definitions.Def_MDPFinance_MeanVariance_TransactionCostValueFunction

open MeasureTheory ProbabilityTheory

namespace MDPFinance.MeanVariance

/-- Theorem 4.5.4 (Bäuerle–Rieder, p. 113, PDF 127). a) `V_n` is concave, increasing and
homogeneous of degree `γ` on `E`, `V_N(x) = U(x_0+x_1)`, `V_n(x) = sup_{0≤a≤x_1+x_0/(1+c)}
𝔼[V_{n+1}(h(x,a)(1+i_{n+1}), a\,\tilde R_{n+1})]`. b) The optimal amount invested in the stock at
time `n` is the three-region rule (4.32) with thresholds `q^±(V_{n+1})` of (4.30)/(4.31). The
thresholds are given through the largest maximizers `a^+_n ∈ [0,1]`, `a^-_n ∈ [0,1/(1+c)]` of the
one-period problems at the states `(0,1)` and `(1,0)` (the book's transformation
`q = a/((1-c)(1-a))`, which also covers `q^+ = ∞`, i.e. `a^+ = 1`): `q^+(V_{n+1}) =
a^+_n/((1-c)(1-a^+_n))` (or `∞`) and `q^-(V_{n+1}) = a^-_n/(1-(1+c)a^-_n)` (or `∞`), and on the
sell region `f_n^*(x) = (x_1 + x_0/(1-c)) a^+_n = (x_0+(1-c)x_1) q^+ / (1+(1-c)q^+)`, on the buy
region `f_n^*(x) = (x_0+(1+c)x_1) a^-_n = (x_0+(1+c)x_1) q^- / (1+(1+c)q^-)`, and `f_n^*(x) = x_1` on
the hold region; the optimal bond holding is `h(x, f_n^*(x))`, and the strategy is optimal. -/
theorem transaction_cost_solution {Ω : Type*} [MeasurableSpace Ω] (M : TransactionCostMarket Ω) :
    (∀ n ≤ M.N, IsInIM M.γ (fun x => M.V n x.1 x.2)) ∧
      (∀ x ∈ Estate, M.V M.N x.1 x.2 = M.U (x.1 + x.2)) ∧
      (∀ n < M.N, ∀ x ∈ Estate,
        M.V n x.1 x.2 = ⨆ a ∈ M.Arange x.1 x.2,
          ∫ ω, M.V (n + 1) (M.h x.1 x.2 a * (1 + M.i (n + 1))) (a * M.Rtilde (n + 1) ω) ∂M.measIP) ∧
      (∃ ap am : ℕ → ℝ, ∀ n < M.N,
        (ap n ∈ Set.Icc (0 : ℝ) 1 ∧
          (∀ a ∈ Set.Icc (0 : ℝ) 1,
            ∫ ω, M.V (n + 1) ((1 - M.c) * (1 - a) * (1 + M.i (n + 1))) (a * M.Rtilde (n + 1) ω)
              ∂M.measIP ≤
            ∫ ω, M.V (n + 1) ((1 - M.c) * (1 - ap n) * (1 + M.i (n + 1)))
              (ap n * M.Rtilde (n + 1) ω) ∂M.measIP) ∧
          (∀ a ∈ Set.Icc (0 : ℝ) 1,
            ∫ ω, M.V (n + 1) ((1 - M.c) * (1 - a) * (1 + M.i (n + 1))) (a * M.Rtilde (n + 1) ω)
              ∂M.measIP =
            ∫ ω, M.V (n + 1) ((1 - M.c) * (1 - ap n) * (1 + M.i (n + 1)))
              (ap n * M.Rtilde (n + 1) ω) ∂M.measIP → a ≤ ap n)) ∧
        (am n ∈ Set.Icc (0 : ℝ) (1 / (1 + M.c)) ∧
          (∀ a ∈ Set.Icc (0 : ℝ) (1 / (1 + M.c)),
            ∫ ω, M.V (n + 1) ((1 - (1 + M.c) * a) * (1 + M.i (n + 1))) (a * M.Rtilde (n + 1) ω)
              ∂M.measIP ≤
            ∫ ω, M.V (n + 1) ((1 - (1 + M.c) * am n) * (1 + M.i (n + 1)))
              (am n * M.Rtilde (n + 1) ω) ∂M.measIP) ∧
          (∀ a ∈ Set.Icc (0 : ℝ) (1 / (1 + M.c)),
            ∫ ω, M.V (n + 1) ((1 - (1 + M.c) * a) * (1 + M.i (n + 1))) (a * M.Rtilde (n + 1) ω)
              ∂M.measIP =
            ∫ ω, M.V (n + 1) ((1 - (1 + M.c) * am n) * (1 + M.i (n + 1)))
              (am n * M.Rtilde (n + 1) ω) ∂M.measIP → a ≤ am n)) ∧
        ∃ fstar : ℕ → ℝ × ℝ → ℝ,
          (∀ n < M.N, ∀ x ∈ Estate,
            let qp : EReal := if ap n < 1 then ((ap n / ((1 - M.c) * (1 - ap n)) : ℝ) : EReal) else ⊤
            let qm : EReal :=
              if am n < 1 / (1 + M.c) then ((am n / (1 - (1 + M.c) * am n) : ℝ) : EReal) else ⊤
            (qp < ratio x.1 x.2 → fstar n x = (x.2 + x.1 / (1 - M.c)) * ap n) ∧
            (qm ≤ ratio x.1 x.2 → ratio x.1 x.2 ≤ qp → fstar n x = x.2) ∧
            (ratio x.1 x.2 < qm → fstar n x = (x.1 + (1 + M.c) * x.2) * am n)) ∧
          M.IsAdmissible 0 fstar ∧
          ∀ x ∈ Estate, M.Vpi fstar 0 x.1 x.2 = M.V 0 x.1 x.2) := by sorry

end MDPFinance.MeanVariance
