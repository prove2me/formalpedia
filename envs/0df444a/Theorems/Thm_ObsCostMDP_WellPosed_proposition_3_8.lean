-- Prove2me | Theorems.Thm_ObsCostMDP_WellPosed_proposition_3_8
-- name    : ObsCostMDP.WellPosed.proposition_3_8
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-13T20:51:37.403001+00:00
-- url     : https://prove2.me/theorems/e24745b4-e993-416a-a7e7-64585e840091
-- title:
--   Proposition 3.8 — comparison principle for the truncated QVI (3.7) when c > 0
-- statement:
--   Let $\tilde F$ be a truncated driver with property (3.5) for some $\beta>0$, let $Q_1,\dots,Q_N$ be substochastic and $c_{a,l}>0$ for all $a,l$. If $u$ is a subsolution and $v$ a supersolution of the truncated QVI (3.7), that is,
--
--   $$\min\{\tilde F_a(u),\,u_a-\mathcal Mu\}\le0,\qquad \min\{\tilde F_a(v),\,v_a-\mathcal Mv\}\ge0$$
--
--   elementwise for every $a\in A$, then $u\le v$ elementwise.
--
--   In particular the truncated QVI has at most one solution; Theorem 3.13 uses this to compare the truncated solutions for different horizons.
--
--   **Formalization Note** No time boundary condition is assumed.
-- source:
--   Reisinger & Tam, Markov decision processes with observation costs: framework and computation with a penalty scheme, arXiv:2201.07908v3, p. 17, Proposition 3.8

import Mathlib
import Definitions.Def_ObsCostMDP_WellPosed_QVI
import Definitions.Def_ObsCostMDP_WellPosed_Truncated

namespace ObsCostMDP.WellPosed

/-- **Proposition 3.8** (Reisinger–Tam, arXiv:2201.07908v3, p. 17), comparison for the truncated
QVI (3.7). Let `F̃` satisfy (3.5) with some `β`, `{Q_n}` be substochastic and `c_{a,l} > 0` for
all `a, l`. If `u` is a subsolution and `v` a supersolution of (3.7), then `u ≤ v`.
**Formalization Note**: no time boundary condition is assumed. -/
theorem proposition_3_8 {N : ℕ} [NeZero N] {X A : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    [Fintype A] [DecidableEq A] [Nonempty A]
    (Ft : TDriver N X A) (β : ℝ) (hFt : Property35 Ft β)
    (Q : Fin N → Matrix X X ℝ) (hQ : IsSubstochasticT Q)
    (c : A → X → ℝ) (hc : ∀ a l, 0 < c a l)
    (u v : Fin N → X → A → ℝ)
    (hsub : IsTSubsolution Ft Q c u) (hsup : IsTSupersolution Ft Q c v) :
    ∀ n l a, u n l a ≤ v n l a := by sorry

end ObsCostMDP.WellPosed
