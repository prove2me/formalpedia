-- Prove2me | Theorems.Thm_Fundraising_Competition_proposition_1
-- name    : Fundraising.Competition.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T08:03:13.330385+00:00
-- url     : https://prove2.me/theorems/6035e81e-f1a4-4d6c-aba7-611f6a0047f6
-- title:
--   Proposition 1, p. 16 — the competition game has a Nash equilibrium, and the equilibria are exactly the solutions of (7)
-- statement:
--   Consider the competition fundraising game between $n$ HOs under the standing hypotheses ($n \ge 1$, $a_i \le b_i$, $B_i > 0$, $z > 0$, $C_i$ strictly increasing and nonnegative on $[0,1]$, $\delta_i$ twice continuously differentiable with $0 < \delta_i \le 1$ on $[a_i,b_i]$) and Assumption 1. Write
--   $$PPD_i(s;x) = \delta_i(s_i)\, z \sum_{a \in A_i} w^a_i\, \theta^{J_a}_i(s).$$
--   Then:
--
--   1. a pure Nash equilibrium $(s;x) \in \prod_i [a_i,b_i] \times [0,1]^n$ of the competition game (each HO solving its lexicographic problem (6)) exists;
--   2. a profile $(s;x) \in \prod_i [a_i,b_i] \times [0,1]^n$ is a Nash equilibrium if and only if, for every HO $i$,
--   $$x_i = \min\left(\frac{B_i}{PPD_i(s;x)},\, 1\right)$$
--   and there are Lagrange multipliers $\lambda_{i1}, \lambda_{i2} \ge 0$ with
--   $$\frac{\delta_i'(s_i)}{\delta_i(s_i)} + \frac{\sum_{a\in A_i} w^a_i\, \partial \theta^{J_a}_i(s)/\partial s_i}{\sum_{a\in A_i} w^a_i\, \theta^{J_a}_i(s)} + \lambda_{i1} - \lambda_{i2} = 0, \qquad \lambda_{i1}(a_i - s_i) = 0, \qquad \lambda_{i2}(s_i - b_i) = 0. \tag{7}$$
--
--   The proposition is the paper's characterization of competitive fundraising: each HO sets its base utility (earmarking) by the KKT conditions of maximizing its unit performance per donor contacted, and the smallest effort that closes its funding gap.
--
--   **Formalization Note.** "The equilibrium is the joint solution of (7)" is formalized as an equivalence for every profile in the strategy box, with existentially quantified multipliers. Derivatives are Mathlib's `deriv`; $\partial\theta^{J}_i/\partial s_i$ is the derivative of $t \mapsto \theta^J_i(s_{-i}, t)$ at $s_i$. The sum over $a\in A_i$ is a sum over contacting sets $J \ni i$. $B_i > 0$ and $\delta_i > 0$ are disclosed additions: with $B_i = 0$ every $s_i$ is a best response and the "only if" fails. The paper writes $\delta(s_i)$ for $\delta_i(s_i)$ in the definition of $PPD_i$. Uniqueness is not claimed.
-- source:
--   Aflaki, Pedraza-Martinez, Competition and Collaboration on Fundraising for Short-Term Disaster Response: The Impact on Earmarking and Performance, SSRN 3705595 (version of December 2022), p. 16, Proposition 1, (7), Assumption 1

import Mathlib
import Definitions.Def_Fundraising_Competition_Setting

namespace Fundraising.Competition

theorem proposition_1 {n : ℕ} (S : Setting n) (hS : Standing S) (hA : Assumption1 S) :
    (∃ s x : Fin n → ℝ, IsNE S s x) ∧
    ∀ s x : Fin n → ℝ, InProfileBox S s x →
      (IsNE S s x ↔ ∀ i : Fin n,
        x i = min (S.B i / PPD S s x i) 1 ∧
        ∃ lam₁ lam₂ : ℝ, 0 ≤ lam₁ ∧ 0 ≤ lam₂ ∧
          deriv (S.δ i) (s i) / S.δ i (s i) +
            (∑ J ∈ contactSets i,
                weight x i J * deriv (fun t => theta (Function.update s i t) J i) (s i)) /
              shareSum s x i + lam₁ - lam₂ = 0 ∧
          lam₁ * (S.a i - s i) = 0 ∧ lam₂ * (s i - S.b i) = 0) := by sorry

end Fundraising.Competition
