-- Prove2me | Theorems.Thm_ObsCostMDP_WellPosed_proposition_3_3
-- name    : ObsCostMDP.WellPosed.proposition_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T20:50:52.625382+00:00
-- url     : https://prove2.me/theorems/52578723-d5f8-4840-b039-05740d46a1ab
-- title:
--   Proposition 3.3 — comparison principle: a bounded subsolution of (3.1) lies below a bounded supersolution when c > 0
-- statement:
--   Let $X$, $A$ be finite and nonempty, let the driver $F$ satisfy Assumption 3.2, let $\{Q_n\}$ be substochastic and $c_{a,x}>0$ for all $a,x$. Suppose $u,v:\mathbb N\times X\to\mathbb R^A$ are bounded, $u$ is a subsolution and $v$ a supersolution of (3.1):
--
--   $$\min\{F_a(n,x,u(n,x),u_a),\,u_a(n,x)-\mathcal Mu(n,x)\}\le0,\qquad \min\{F_a(n,x,v(n,x),v_a),\,v_a(n,x)-\mathcal Mv(n,x)\}\ge0$$
--
--   for all $n\in\mathbb N$, $x\in X$, $a\in A$. Then $u\le v$, that is, $u_a(n,x)\le v_a(n,x)$ for all $n,x,a$.
--
--   This comparison principle gives uniqueness of bounded solutions of Problem 3.1.
-- source:
--   Reisinger & Tam, Markov decision processes with observation costs: framework and computation with a penalty scheme, arXiv:2201.07908v3, p. 15, Proposition 3.3

import Mathlib
import Definitions.Def_ObsCostMDP_WellPosed_QVI

namespace ObsCostMDP.WellPosed

/-- **Proposition 3.3** (Reisinger–Tam, arXiv:2201.07908v3, p. 15), comparison principle for (3.1).
Under Assumption 3.2, with `{Q_n}` substochastic and `c_{a,x} > 0` for all `a, x`: if `u` is a
bounded subsolution and `v` a bounded supersolution of (3.1), then `u ≤ v` pointwise. -/
theorem proposition_3_3 {X A : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    [Fintype A] [DecidableEq A] [Nonempty A]
    (F : Driver X A) (β : ℝ) (hF : Assumption32 F β)
    (Q : ℕ → Matrix X X ℝ) (hQ : IsSubstochastic Q)
    (c : A → X → ℝ) (hc : ∀ a x, 0 < c a x)
    (u v : ℕ → X → A → ℝ) (hu : IsBounded u) (hv : IsBounded v)
    (hsub : IsSubsolution F Q c u) (hsup : IsSupersolution F Q c v) :
    ∀ n x a, u n x a ≤ v n x a := by sorry

end ObsCostMDP.WellPosed
