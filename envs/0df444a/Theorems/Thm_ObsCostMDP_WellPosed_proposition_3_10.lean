-- Prove2me | Theorems.Thm_ObsCostMDP_WellPosed_proposition_3_10
-- name    : ObsCostMDP.WellPosed.proposition_3_10
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-13T20:51:37.450461+00:00
-- url     : https://prove2.me/theorems/eac8cbbb-e70f-4584-84d2-70110a7842df
-- title:
--   Proposition 3.10 — comparison principle for the penalised problem (3.8), every ρ ≥ 0
-- statement:
--   Let $\tilde F$ be a truncated driver with property (3.5) for some $\beta>0$, let $Q_1,\dots,Q_N$ be substochastic, $c\in\mathbb R^{L\times d}$ arbitrary and $\pi$ a penalisation function. Let $\rho\ge0$. If $u^\rho$ is a subsolution and $v^\rho$ a supersolution of the penalised problem (3.8), that is,
--
--   $$\tilde F_a(u^\rho)-\rho\,\pi(\mathcal Mu^\rho-u^\rho_a)\le0,\qquad \tilde F_a(v^\rho)-\rho\,\pi(\mathcal Mv^\rho-v^\rho_a)\ge0$$
--
--   elementwise for every $a\in A$, then $u^\rho\le v^\rho$ elementwise.
--
--   In particular (3.8) has at most one solution for each $\rho\ge0$, and the solutions are non-decreasing in $\rho$; this is the step of Theorem 3.13 that makes the penalty limit monotone.
-- source:
--   Reisinger & Tam, Markov decision processes with observation costs: framework and computation with a penalty scheme, arXiv:2201.07908v3, p. 18, Proposition 3.10

import Mathlib
import Definitions.Def_ObsCostMDP_WellPosed_QVI
import Definitions.Def_ObsCostMDP_WellPosed_Truncated

namespace ObsCostMDP.WellPosed

/-- **Proposition 3.10** (Reisinger–Tam, arXiv:2201.07908v3, p. 18), comparison for the penalised
problem (3.8). Let `F̃` satisfy (3.5) with some `β`, `{Q_n}` be substochastic, `c` arbitrary and
`π` a penalisation function. For every `ρ ≥ 0`, a subsolution `u^ρ` of (3.8) lies below a
supersolution `v^ρ` of (3.8). -/
theorem proposition_3_10 {N : ℕ} [NeZero N] {X A : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    [Fintype A] [DecidableEq A] [Nonempty A]
    (Ft : TDriver N X A) (β : ℝ) (hFt : Property35 Ft β)
    (Q : Fin N → Matrix X X ℝ) (hQ : IsSubstochasticT Q)
    (c : A → X → ℝ) (pen : ℝ → ℝ) (hpen : IsPenalty pen) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (u v : Fin N → X → A → ℝ)
    (hsub : IsPenSubsolution Ft Q c pen ρ u) (hsup : IsPenSupersolution Ft Q c pen ρ v) :
    ∀ n l a, u n l a ≤ v n l a := by sorry

end ObsCostMDP.WellPosed
