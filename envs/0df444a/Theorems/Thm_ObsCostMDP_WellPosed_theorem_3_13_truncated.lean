-- Prove2me | Theorems.Thm_ObsCostMDP_WellPosed_theorem_3_13_truncated
-- name    : ObsCostMDP.WellPosed.theorem_3_13_truncated
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T20:51:45.667178+00:00
-- url     : https://prove2.me/theorems/2578d6b1-5706-4804-9a1d-36e82884e2e9
-- title:
--   Theorem 3.13, truncated assertion — u^{ρ,N} is unique, increases to u^N as ρ → ∞, and u^N solves (3.7) when c > 0
-- statement:
--   Let $\tilde F$ be a truncated driver whose components $\tilde F_a:\mathbb R^{N\times L\times d}\to\mathbb R^{N\times L}$ are continuous and which has property (3.5) for some $\beta>0$. Let $Q_1,\dots,Q_N$ be substochastic, $c_{a,l}\ge0$ for all $a,l$, and $\pi$ a penalisation function. Then:
--
--   1. for every $\rho\ge0$ the penalised problem (3.8) has exactly one solution $u^{\rho,N}$;
--   2. $\rho\mapsto u^{\rho,N}$ is non-decreasing on $[0,\infty)$, elementwise;
--   3. the limit $u^N=\lim_{\rho\to\infty}u^{\rho,N}$ exists, elementwise;
--   4. if moreover $c_{a,l}>0$ for all $a,l$, then $u^N$ solves the truncated QVI (3.7):
--   $$\min\{\tilde F_a(u^N),\,u^N_a-\mathcal Mu^N\}=0\quad\text{elementwise, for every }a\in A.$$
--
--   This is the truncated half of Theorem 3.13: the penalty method converges monotonically from below to a solution of the finite QVI.
--
--   **Formalization Note** $\tilde F$ is abstract, as in Problems 3.6 and 3.9, not necessarily the restriction of a driver of Problem 3.1. The limit is taken along $\rho\to\infty$ in $\mathbb R$. The time boundary condition $u_a(N,\cdot)=\mathcal Mu(N,\cdot)$ of Problem 3.6 is not claimed for $u^N$.
-- source:
--   Reisinger & Tam, Markov decision processes with observation costs: framework and computation with a penalty scheme, arXiv:2201.07908v3, p. 19, Theorem 3.13 (assertion on u^N = lim_{ρ→∞} u^{ρ,N}) and its proof

import Mathlib
import Definitions.Def_ObsCostMDP_WellPosed_QVI
import Definitions.Def_ObsCostMDP_WellPosed_Truncated

open Filter Topology

namespace ObsCostMDP.WellPosed

/-- **Theorem 3.13, truncated assertion** (Reisinger–Tam, arXiv:2201.07908v3, p. 19). Let `F̃` be
continuous and satisfy (3.5) with constant `β`, `{Q_n}` substochastic, `c_{a,l} ≥ 0` for all
`a, l` and `π` a penalisation function. Then there are `ρ ↦ u^ρ` and `u^N` such that
(a) for every `ρ ≥ 0`, `u^ρ` is the unique solution of the penalised problem (3.8);
(b) `ρ ↦ u^ρ` is non-decreasing on `[0, ∞)` (monotone convergence from below);
(c) `u^ρ → u^N` (pointwise, i.e. in the product topology) as `ρ → ∞`;
(d) if moreover `c_{a,l} > 0` for all `a, l`, then `u^N` solves (3.7).
**Formalization Note**: `F̃` is abstract (Problems 3.6, 3.9), not the restriction of a driver of
Problem 3.1. The time boundary condition `u_a(N, ·) = Mu(N, ·)` of Problem 3.6 is not part of (d). -/
theorem theorem_3_13_truncated {N : ℕ} [NeZero N] {X A : Type*} [Fintype X] [DecidableEq X]
    [Nonempty X] [Fintype A] [DecidableEq A] [Nonempty A]
    (Ft : TDriver N X A) (hcont : ∀ a, Continuous (Ft a)) (β : ℝ) (hFt : Property35 Ft β)
    (Q : Fin N → Matrix X X ℝ) (hQ : IsSubstochasticT Q)
    (c : A → X → ℝ) (hc : ∀ a l, 0 ≤ c a l) (pen : ℝ → ℝ) (hpen : IsPenalty pen) :
    ∃ (U : ℝ → Fin N → X → A → ℝ) (uN : Fin N → X → A → ℝ),
      (∀ ρ, 0 ≤ ρ → IsPenSolution Ft Q c pen ρ (U ρ) ∧
        ∀ w, IsPenSolution Ft Q c pen ρ w → w = U ρ) ∧
      MonotoneOn U (Set.Ici 0) ∧
      Tendsto U atTop (𝓝 uN) ∧
      ((∀ a l, 0 < c a l) → IsTSolution Ft Q c uN) := by sorry

end ObsCostMDP.WellPosed
