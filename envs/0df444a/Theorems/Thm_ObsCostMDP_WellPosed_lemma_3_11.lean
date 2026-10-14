-- Prove2me | Theorems.Thm_ObsCostMDP_WellPosed_lemma_3_11
-- name    : ObsCostMDP.WellPosed.lemma_3_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T20:51:37.560235+00:00
-- url     : https://prove2.me/theorems/af453458-9479-4382-baaf-b532f9d57f31
-- title:
--   Lemma 3.11 — a solution of the penalised problem satisfies ‖u^ρ‖ ≤ ‖F̃(0)‖/β when c ≥ 0
-- statement:
--   Let $\tilde F$ be a truncated driver with property (3.5) for the constant $\beta>0$, let $Q_1,\dots,Q_N$ be substochastic, $c_{a,l}\ge0$ for all $a,l$, $\pi$ a penalisation function and $\rho\ge0$. If $u^\rho$ solves the penalised problem (3.8), then
--
--   $$\|u^\rho\|_\infty\le\frac{\|\tilde F(0)\|_\infty}{\beta},$$
--
--   where $\|\cdot\|_\infty$ is the maximum absolute entry and $\tilde F(0)$ collects $\tilde F_a(0)^n_l$ over all $a,n,l$.
--
--   The bound is uniform in $\rho$; together with the monotonicity from Proposition 3.10 it yields convergence of the penalised solutions as $\rho\to\infty$.
--
--   **Formalization Note** The norms are written out: for any $K$ with $|\tilde F_a(0)^n_l|\le K$ for all $a,n,l$ (in particular $K=\|\tilde F(0)\|_\infty$), every entry satisfies $|u^n_{a,l}|\le K/\beta$. The paper's "the solution" is read as "every solution".
-- source:
--   Reisinger & Tam, Markov decision processes with observation costs: framework and computation with a penalty scheme, arXiv:2201.07908v3, p. 19, Lemma 3.11

import Mathlib
import Definitions.Def_ObsCostMDP_WellPosed_QVI
import Definitions.Def_ObsCostMDP_WellPosed_Truncated

namespace ObsCostMDP.WellPosed

/-- **Lemma 3.11** (Reisinger–Tam, arXiv:2201.07908v3, p. 19), a-priori bound. Let `F̃` satisfy
(3.5) with constant `β`, `{Q_n}` be substochastic, `c_{a,l} ≥ 0` for all `a, l`, `π` a penalisation
function and `ρ ≥ 0`. Every solution `u` of (3.8) satisfies `‖u‖_∞ ≤ ‖F̃(0)‖_∞ / β`.
**Formalization Note**: the sup norms are written out: `K` is any bound on
`|F̃_a(0)^n_l|` over all `a, n, l` (in particular `‖F̃(0)‖_∞` itself), and the conclusion bounds
`|u^n_{a,l}|` for all `n, l, a`. -/
theorem lemma_3_11 {N : ℕ} [NeZero N] {X A : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    [Fintype A] [DecidableEq A] [Nonempty A]
    (Ft : TDriver N X A) (β : ℝ) (hFt : Property35 Ft β)
    (Q : Fin N → Matrix X X ℝ) (hQ : IsSubstochasticT Q)
    (c : A → X → ℝ) (hc : ∀ a l, 0 ≤ c a l) (pen : ℝ → ℝ) (hpen : IsPenalty pen)
    (ρ : ℝ) (hρ : 0 ≤ ρ) (u : Fin N → X → A → ℝ) (hu : IsPenSolution Ft Q c pen ρ u)
    (K : ℝ) (hK : ∀ a n l, |Ft a (fun _ _ _ => 0) n l| ≤ K) :
    ∀ n l a, |u n l a| ≤ K / β := by sorry

end ObsCostMDP.WellPosed
