-- Prove2me | Theorems.Thm_MDPFinance_OptimalStopping_theorem_10_2_2
-- name    : MDPFinance.OptimalStopping.theorem_10_2_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T23:45:00.061698+00:00
-- url     : https://prove2.me/theorems/3e96f6f6-7fc9-4c11-ac5e-7f442ba54b55
-- title:
--   Theorem 10.2.2 — the value is the smallest c-superharmonic majorant of g
-- statement:
--   **Theorem 10.2.2** (p. 311). Suppose a stopping problem with unbounded horizon is given.
--   Then it holds:
--
--   a) $V_\infty^*(x) = G(x) = J(x)$ for all $x \in E$.
--   b) $J = \mathcal{T}J$, i.e.
--      $J(x) = \max\{g(x),\ c(x) + \beta\int J(x')Q^X(dx'|x)\}$, $x \in E$.
--   c) $J$ is the smallest $c$-superharmonic function which majorizes $g$, i.e. $J$ is the smallest
--      function such that for all $x \in E$
--      $$ J(x) \ge c(x) + \beta\int J(x')Q^X(dx'|x) \quad\text{and}\quad J(x) \ge g(x). $$
--
--   This is the Snell-envelope characterization of an optimal stopping problem's value, and the
--   abstract result the rest of the chapter instantiates: Chapter 11's perpetual American put is the
--   same statement for the payoff $(K-x)^+$.
--
--   Three things are load-bearing.
--
--   **a) is a three-way equality of three genuinely different objects.** $V_\infty^*$ is the supremum
--   over almost surely finite stopping times of $\mathbb{E}_x[R_\tau]$ **(10.3)**;
--   $G = \sup_\pi G_\pi$ with $G_\pi = \liminf_n J_{n\pi}$ is a supremum over policies of a $\liminf$
--   of finite-horizon values; and $J = \lim_n J_n$ is the limit of the value iteration. Nothing about
--   the three definitions makes them obviously equal, and the proof needs both halves of Assumption
--   (B).
--
--   **c) is a minimality claim with two conjuncts.** $c$-superharmonic means
--   $v \ge c + \beta\int v\,dQ^X$; majorizing $g$ means $v \ge g$. Asserting only one of them, or
--   asserting that $J$ *is* such a function without minimality over all of them, is a strictly weaker
--   and different statement. The minimality is a universally quantified comparison against every
--   competitor with both properties.
--
--   **b) is not implied by c).** The fixed point equation $J = \mathcal{T}J$ is an equality; c) gives
--   only the two inequalities plus minimality. Both are in the book's statement.
--
--   **Moderation note.** The draft's `J` and `G` were free functions tied to the model only through a real limit and an `IsLUB` over Markov policies (the book's `G` is over all policies, history-dependent ones included, which the proof uses). Now `J := sup_n J_n`, `G := sup_τ liminf_n 𝔼_x[R_{τ∧n}]`, `V_∞^*` the supremum over a.s.-finite stopping times, all in `[-∞,∞]`; c) is minimality among `[-∞,∞]`-valued `c`-superharmonic majorants of `g`.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 311 (PDF 319), Theorem 10.2.2

import Mathlib
import Definitions.Def_MDPFinance_OptimalStopping_Stationary

open MeasureTheory Filter Topology

namespace MDPFinance.OptimalStopping

/-- **Theorem 10.2.2** (p. 311), under Assumption (B). a) `V_∞^* = G = J` with `J := lim_n J_n`
and `G := sup_π liminf_n J_{nπ}`. b) `J = T J`. c) `J` is the smallest `c`-superharmonic
function majorizing `g`. -/
theorem theorem_10_2_2 {E : Type*} [MeasurableSpace E] (P : StationaryProblem E)
    (Pr : E → Measure (ℕ → E)) (hPr : P.IsPathLaw Pr) (hB : P.AssumptionB Pr) :
    (∀ x : E, P.Vstar Pr x = P.Jlim x ∧ P.G Pr x = P.Jlim x) ∧
    (∀ x : E, P.Jlim x = P.T P.Jlim x) ∧
    (P.Superharmonic P.Jlim ∧ (∀ x : E, (P.g x : EReal) ≤ P.Jlim x) ∧
      ∀ v : E → EReal, P.Superharmonic v → (∀ x : E, (P.g x : EReal) ≤ v x) →
        ∀ x : E, P.Jlim x ≤ v x) := by sorry

end MDPFinance.OptimalStopping
