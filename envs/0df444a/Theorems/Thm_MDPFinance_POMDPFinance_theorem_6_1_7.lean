-- Prove2me | Theorems.Thm_MDPFinance_POMDPFinance_theorem_6_1_7
-- name    : MDPFinance.POMDPFinance.theorem_6_1_7
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T22:36:13.456416+00:00
-- url     : https://prove2.me/theorems/c6ba908f-96f6-4a89-b813-5a4dedc2025b
-- title:
--   Theorem 6.1.7 — logarithmic-utility closed form under partial observation
-- statement:
--   For the logarithmic utility $U(x) = \log(x)$, the value function again factors:
--   $J_k(x,\rho) = \log(x) + d_k(\rho)$, where $(d_k)$ is the belief-only recursion (6.6) of
--   `MDPFinance.POMDPFinance.dLog`. As in the power-utility case (Theorem 6.1.2), the additive
--   (rather than multiplicative) separability of the logarithm lets the wealth dependence factor out
--   of the optimization entirely.
--
--   If $\alpha$ maximizes the pure log-return objective $\int \log(1+\alpha\cdot z)\,
--   d(\text{predictive}(\rho))(z)$ over the admissible set, then the amount $x\alpha$ maximizes the
--   original Bellman equation's right-hand side at every wealth $x \ge 0$ and every stage $k$: unlike
--   the power-utility case, the maximizer here is genuinely stage-independent, since the recursion's
--   continuation value $d_{k-1}(\Phi(\rho,z))$ enters the one-step objective additively and so drops
--   out of the argmax over $\alpha$ entirely — the book's own remark that "the optimal amounts
--   invested do not depend on $n$."
--
--   **Moderation note.** State claims for $x>0$ ($\operatorname{dom}U=(0,\infty)$) and $\rho\in\mathbb P(E_Y)$; values and the one-step objective $\int\log(1+\alpha\cdot z)$ in $[-\infty,\infty]$; the maximizer in $\tilde A$; and the optimality of the strategy built from any measurable selection $\alpha^*(\cdot)$ of maximizers is stated.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 181, Theorem 6.1.7

import Mathlib
import Definitions.Def_MDPFinance_POMDPFinance_Filter
import Definitions.Def_MDPFinance_POMDPFinance_HistPolicy
import Definitions.Def_MDPFinance_POMDPFinance_TerminalWealth
import Definitions.Def_MDPFinance_POMDPFinance_PowerLogValue

open MeasureTheory ProbabilityTheory

namespace MDPFinance.POMDPFinance

/-- Theorem 6.1.7 (Bäuerle–Rieder, p. 181, PDF 195). Let `U` be the logarithmic utility. Then it
holds: a) The value functions are given by `J_n(x,\rho) = \log(x) + d_n(\rho)`, `(x,\rho) \in E_X
\times ℙ(E_Y)` where `(d_n)` satisfies the recursion (6.6). b) The optimal amounts which are
invested in the stocks are given by `f_n^*(x,\rho) = \alpha^*(\rho)x`, `x \ge 0` where
`\alpha^*(\rho)` is a maximiser of (6.6); the optimal portfolio strategy is given by
`(f_0,\dots,f_{N-1})` where `f_n(h_n):=f_{N-n}^*(x_n,\mu_n(\cdot|h_n))`. Note (the book's own
remark) that the optimal amounts invested do not depend on `n`; this is not separately asserted
here since `\alpha^*(\rho)` (the maximiser in `AtildeLog`) is already stated without an `n`/`k`
subscript, matching the book's own notation `\alpha^*(\rho)` (vs. `\alpha_n^*(\rho)` for the power
case, Theorem 6.1.2), even though the *value* `d_k(\rho)` used to check optimality still varies
with `k` (the recursion (6.6) for `d_k` still needs the horizon; only the maximiser is horizon-free
once the objective's optimality condition is checked pointwise, since (6.6)'s inner supremand
`\log(1+\alpha\cdot z)` does not involve `d_{k-1}` in the argument being maximized over `\alpha`).
State claims on `E_X × ℙ(E_Y)` (`x > 0`, `ρ` a probability measure), values and the one-step
objective in `[-∞,∞]`; the maximizer is taken in `\tilde A`; and the strategy built from any
measurable selection `α^*(\cdot)` of maximizers is optimal. -/
theorem theorem_6_1_7 {EY : Type*} [MeasurableSpace EY] {d : ℕ} (M : FilterMarket EY d)
    (Fd : FilterOp M) (Mk : TerminalWealthMarket M) (hU : Mk.U = Real.log)
    (hdomU : Mk.domU = Set.Ioi 0) (N : ℕ) :
    (∀ k ≤ N, ∀ x > (0 : ℝ), ∀ ρ : Measure EY, IsProbabilityMeasure ρ →
        Jsup M Fd (fun _ => Mk.i) Mk.U Mk.D k x ρ = (Real.log x : EReal) + dLog M Fd Mk.i k ρ) ∧
      (∀ ρ : Measure EY, IsProbabilityMeasure ρ → ∀ α ∈ AtildeLog M,
        IsMaxOn (fun a => erealIntegral (M.predictive ρ) fun z =>
            ((Real.log (1 + ∑ j, a j * z j) : ℝ) : EReal)) (AtildeLog M) α →
        ∀ k < N, ∀ x > (0 : ℝ), IsMaxOn
          (fun a => erealIntegral (M.predictive ρ) fun z =>
            Jsup M Fd (fun _ => Mk.i) Mk.U Mk.D k ((1 + Mk.i) * (x + ∑ j, a j * z j)) (Fd.Phi ρ z))
          (Mk.D x) (fun j => x * α j)) ∧
      (∀ αs : Measure EY → Fin d → ℝ,
        Measurable (fun p : ℝ × Measure EY => fun j => p.1 * αs p.2 j) →
        (∀ ρ : Measure EY, IsProbabilityMeasure ρ → αs ρ ∈ AtildeLog M ∧
          IsMaxOn (fun a => erealIntegral (M.predictive ρ) fun z =>
            ((Real.log (1 + ∑ j, a j * z j) : ℝ) : EReal)) (AtildeLog M) (αs ρ)) →
        ∀ x0 > (0 : ℝ), Vpi M Fd (fun _ => Mk.i) Mk.U
            (ofMarkov M Fd (fun _ => Mk.i) x0 fun _ p => fun j => p.1 * αs p.2 j)
            N 0 (fun _ => 0) x0 M.Q0 =
          Jsup M Fd (fun _ => Mk.i) Mk.U Mk.D N x0 M.Q0) := by sorry

end MDPFinance.POMDPFinance
