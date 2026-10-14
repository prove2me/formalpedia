-- Prove2me | Theorems.Thm_ObsCostMDP_WellPosed_theorem_3_13
-- name    : ObsCostMDP.WellPosed.theorem_3_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T20:50:50.678949+00:00
-- url     : https://prove2.me/theorems/a83332a7-0887-4fef-b30b-c2bdda9b71b2
-- title:
--   Theorem 3.13 — for c > 0 the QVI (3.1) has exactly one bounded solution
-- statement:
--   Let $X$ and $A$ be finite and nonempty, let the driver $F=\{F_a\}_{a\in A}$ satisfy Assumption 3.2 (with some $\beta>0$) and Assumption 3.12, and suppose in addition that
--
--   $$\sup_{a\in A,\,n\in\mathbb N,\,x\in X}\big|F_a(n,x,0,0)\big|<\infty,$$
--
--   where the first $0$ is the zero vector of $\mathbb R^A$ and the second the zero function on $\mathbb N\times X$. Let $\{Q_n\}$ be substochastic and $c_{a,x}>0$ for all $a,x$. Then the QVI (3.1),
--
--   $$\min\{F_a(n,x,u(n,x),u_a),\,u_a(n,x)-\mathcal Mu(n,x)\}=0,\qquad n\in\mathbb N,\ x\in X,\ a\in A,$$
--
--   has a bounded solution $u:\mathbb N\times X\to\mathbb R^A$, and every bounded solution equals $u$.
--
--   This is the well-posedness of the abstract QVI that covers the observation cost model; the paper obtains the solution as the limit of truncated, penalised problems.
--
--   **Formalization Note** "Well-posed" is read as existence and uniqueness in the class of bounded functions. The uniform bound on $F_a(n,x,0,0)$ is an added hypothesis: Assumption 3.2.2 bounds $x\mapsto F_a(n,x,r,\phi)$ for each fixed $n$ only, and with that reading the theorem fails (e.g. $F_a(n,x,r,\phi)=r_a-\gamma\phi(n+1,x)-n$ admits no bounded solution). The construction $u=\lim_{N\to\infty}\lim_{\rho\to\infty}u^{\rho,N}$ described in the theorem is not part of this statement; the penalty limit is the separate item `theorem_3_13_truncated`.
-- source:
--   Reisinger & Tam, Markov decision processes with observation costs: framework and computation with a penalty scheme, arXiv:2201.07908v3, p. 19, Theorem 3.13

import Mathlib
import Definitions.Def_ObsCostMDP_WellPosed_QVI

namespace ObsCostMDP.WellPosed

/-- **Theorem 3.13** (Reisinger–Tam, arXiv:2201.07908v3, p. 19), well-posedness of the QVI (3.1).
Let `X`, `A` be finite and nonempty, `F` a driver satisfying Assumption 3.2 (with constant `β`)
and Assumption 3.12, `{Q_n}` substochastic and `c_{a,x} > 0` for all `a, x`. Then (3.1) has exactly
one bounded solution.
**Formalization Note**: "well-posed" is read as existence and uniqueness of a bounded solution.
The hypothesis `hF0` (`|F_a(n, x, 0, 0)| ≤ K` uniformly in `a, n, x`) is added: it is the uniform
reading of the boundedness in Assumption 3.2.2, which the proof uses ("By Lemma 3.11, u^N is also
bounded above, independent of N"); without it the theorem is false. The construction of the
solution as `lim_{N→∞} lim_{ρ→∞} u^{ρ,N}` is not part of this statement. -/
theorem theorem_3_13 {X A : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    [Fintype A] [DecidableEq A] [Nonempty A]
    (F : Driver X A) (β : ℝ) (hF : Assumption32 F β) (hF' : Assumption312 F)
    (hF0 : ∃ K : ℝ, ∀ a n x, |F a n x (fun _ => 0) (fun _ _ => 0)| ≤ K)
    (Q : ℕ → Matrix X X ℝ) (hQ : IsSubstochastic Q)
    (c : A → X → ℝ) (hc : ∀ a x, 0 < c a x) :
    ∃ u : ℕ → X → A → ℝ, IsBounded u ∧ IsSolution F Q c u ∧
      ∀ v : ℕ → X → A → ℝ, IsBounded v → IsSolution F Q c v → v = u := by sorry

end ObsCostMDP.WellPosed
