-- Prove2me | Theorems.Thm_MDPFinance_POMDPFinance_theorem_6_1_2
-- name    : MDPFinance.POMDPFinance.theorem_6_1_2
-- status  : Disproved
-- author  : @Shuze Chen
-- created : 2026-09-27T22:36:23.2153+00:00
-- url     : https://prove2.me/theorems/9e8b225f-b2a2-4d03-9b09-2c47b38c74ed
-- title:
--   Theorem 6.1.2 — power-utility closed form under partial observation
-- statement:
--   For the power utility $U(x) = x^\gamma/\gamma$, $0<\gamma<1$, the general value function of
--   Theorem 6.1.1 factors explicitly: $J_k(x,\rho) = (x(1+i)^k)^\gamma\,d_k(\rho)$, where $(d_k)$ is
--   the belief-only recursion (6.3) of `MDPFinance.POMDPFinance.dPow`. This is the partial-observation
--   analogue of the classical power-utility solution (compare chunk `04a`'s Theorem 4.2.6): the
--   homogeneity of the power function lets the wealth dependence separate out entirely, leaving a
--   pure filtering problem for the multiplicative factor $d_k$.
--
--   The optimal invested fraction is likewise explicit: if $\alpha$ maximizes $d_k$'s own one-step
--   objective $\int d_k(\Phi(\rho,z))(1+\alpha\cdot z)^\gamma\,d(\text{predictive}(\rho))(z)$ over
--   the admissible set $\tilde A$, then the *amount* $x\alpha$ maximizes the original Bellman
--   equation's right-hand side at wealth $x \ge 0$ — the optimal portfolio strategy invests a
--   belief-dependent, wealth-proportional fraction in the stocks.
--
--   **Formalization Note.** The transfer from the $d_k$-level maximizer $\alpha$ to the
--   wealth-level maximizer $x\alpha$ is a homogeneity argument (the original objective, expressed in
--   terms of $\alpha := a/x$, differs from $d_k$'s own objective only by additive and multiplicative
--   constants independent of $\alpha$), stated here as the theorem's substantive content rather than
--   assumed.
--
--   **Moderation note.** State claims for $x\ge 0$ and $\rho\in\mathbb P(E_Y)$ (for $x<0$ the feasible set is empty under no arbitrage and the value is $-\infty$, not $(x(1+i)^k)^\gamma d_k$); the maximizer $\alpha$ is taken in $\tilde A$; and the optimality of the strategy $f_n(h_n)=\alpha^*_{N-n}(\mu_n)x_n$ built from any measurable selection of maximizers, which the book's part b) asserts, is now stated.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 178, Theorem 6.1.2

import Mathlib
import Definitions.Def_MDPFinance_POMDPFinance_Filter
import Definitions.Def_MDPFinance_POMDPFinance_HistPolicy
import Definitions.Def_MDPFinance_POMDPFinance_TerminalWealth
import Definitions.Def_MDPFinance_POMDPFinance_PowerLogValue

open MeasureTheory ProbabilityTheory

namespace MDPFinance.POMDPFinance

/-- Theorem 6.1.2 (Bäuerle–Rieder, p. 178, PDF 191). Let `U` be the power utility with `0 < γ <
1`. Then it holds: a) The value functions are given by `J_n(x,ρ) = (xS^0_n)^γ d_n(ρ)`, `(x,ρ) \in
E_X \times ℙ(E_Y)` where the sequence `(d_n)` satisfies the recursion (6.3). b) The optimal
amounts which are invested in the stocks are given by `f_n^*(x,ρ) = α_n^*(ρ)x`, `x \ge 0` where
`α_n^*(ρ)` is a maximiser of (6.3); the optimal portfolio strategy is given by
`(f_0,\dots,f_{N-1})` where `f_n(h_n) := f_{N-n}^*(x_n,μ_n(\cdot|h_n))`. `S^0_n \equiv (1+i)^n`
here (constant rate), so `J_k(x,ρ) = (x(1+i)^k)^γ \, d_k(ρ)` with `k` stages remaining, matching
`dPow`'s own indexing. State claims on `E_X × ℙ(E_Y)` (`x ≥ 0`, `ρ` a probability measure); the
maximizer `α` is taken in `\tilde A`; and the strategy `f_n(h_n) := α^*_{N-n}(μ_n) x_n` built
from any measurable selection of maximizers is optimal for the `N`-stage problem. -/
theorem theorem_6_1_2 {EY : Type*} [MeasurableSpace EY] {d : ℕ} (M : FilterMarket EY d)
    (Fd : FilterOp M) (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1) (Mk : TerminalWealthMarket M)
    (hU : Mk.U = fun x => x ^ γ / γ) (hdomU : Mk.domU = Set.Ici 0) (N : ℕ) :
    (∀ k ≤ N, ∀ x ≥ (0 : ℝ), ∀ ρ : Measure EY, IsProbabilityMeasure ρ →
        Jsup M Fd (fun _ => Mk.i) Mk.U Mk.D k x ρ =
          (((x * (1 + Mk.i) ^ k) ^ γ * dPow M Fd γ k ρ : ℝ) : EReal)) ∧
      (∀ k < N, ∀ ρ : Measure EY, IsProbabilityMeasure ρ → ∀ α ∈ AtildePow M,
        IsMaxOn (fun a => ∫ z, dPow M Fd γ k (Fd.Phi ρ z) * (1 + ∑ j, a j * z j) ^ γ
            ∂(M.predictive ρ)) (AtildePow M) α →
        ∀ x ≥ (0 : ℝ), IsMaxOn
          (fun a => erealIntegral (M.predictive ρ) fun z =>
            Jsup M Fd (fun _ => Mk.i) Mk.U Mk.D k ((1 + Mk.i) * (x + ∑ j, a j * z j)) (Fd.Phi ρ z))
          (Mk.D x) (fun j => x * α j)) ∧
      (∀ αs : ℕ → Measure EY → Fin d → ℝ,
        (∀ k < N, Measurable (fun p : ℝ × Measure EY => fun j => p.1 * αs k p.2 j) ∧
          ∀ ρ : Measure EY, IsProbabilityMeasure ρ → αs k ρ ∈ AtildePow M ∧
            IsMaxOn (fun a => ∫ z, dPow M Fd γ k (Fd.Phi ρ z) * (1 + ∑ j, a j * z j) ^ γ
              ∂(M.predictive ρ)) (AtildePow M) (αs k ρ)) →
        ∀ x0 ≥ (0 : ℝ), Vpi M Fd (fun _ => Mk.i) Mk.U
            (ofMarkov M Fd (fun _ => Mk.i) x0 fun k p => fun j => p.1 * αs (N - k) p.2 j)
            N 0 (fun _ => 0) x0 M.Q0 =
          Jsup M Fd (fun _ => Mk.i) Mk.U Mk.D N x0 M.Q0) := by sorry

end MDPFinance.POMDPFinance
