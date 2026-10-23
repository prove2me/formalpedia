-- Prove2me | Theorems.Thm_Orabona2019_theorem_12_5_faithful
-- name    : Orabona2019.theorem_12_5_faithful
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-23T00:30:54.778656+00:00
-- url     : https://prove2.me/theorems/bb70bd5d-95fc-4f50-9d54-efd26f6f11a5
-- title:
--   Theorem 12.5, with the surrogate-subgradient bound
-- statement:
--   Let $E$ be a finite-dimensional real normed space with dual norm $\|\cdot\|_\star$, and let $V\subseteq W\subseteq E$ with $V$ non-empty, closed and convex; write $\mathrm{dist}_V$ for the distance to $V$. Fix $T\ge1$ and consider a run of the constrained-to-unconstrained reduction (Algorithm 12.1): on each round $t=1,\dots,T$ the unconstrained learner proposes $z_t\in W$, the learner plays a nearest point $x_t\in V$ of $z_t$, $g_t$ is a subgradient of the loss $\ell_t$ at $x_t$ relative to $V$, and $q_t$ is a subgradient of $\mathrm{dist}_V$ at $z_t$. Let $\tilde\ell^{(1)}_t,\dots,\tilde\ell^{(4)}_t$ be the four surrogate losses of Theorem 12.5, for example $\tilde\ell^{(1)}_t(w)=\langle g_t,w\rangle+\|g_t\|_\star\,\mathrm{dist}_V(w)$ and $\tilde\ell^{(2)}_t(w)=\langle g_t+\|g_t\|_\star q_t,w\rangle$. Then for each $k=1,\dots,4$:
--
--   1. for every $u\in V$, $$\sum_{t=1}^T\big(\ell_t(x_t)-\ell_t(u)\big)\le\sum_{t=1}^T\big(\tilde\ell^{(k)}_t(z_t)-\tilde\ell^{(k)}_t(u)\big);$$
--   2. for every $t$, every $y\in W$ and every subgradient $\tilde g$ of $\tilde\ell^{(k)}_t$ at $y$, $$\|\tilde g\|_\star\le2\|g_t\|_\star.$$
--
--   This is Theorem 12.5 of Orabona's book with both of its conclusions: the regret of the constrained learner is dominated by the regret of the unconstrained learner on the surrogates, and the surrogates are at most twice as Lipschitz as the original losses, so the unconstrained learner's Lipschitz-based guarantee applies to them. The existing theorem ModernOnlineLearning.Reductions.theorem_12_5 is part 1.
--
--   **Formalization Note** Subgradients of the surrogates in part 2 are full-space subgradients of the printed formulas on $E$.
-- source:
--   Orabona, A Modern Introduction to Online Learning, arXiv:1912.13213v10, pp. 195–196, Theorem 12.5

import Mathlib
import Definitions.Def_ModernOnlineLearning_OGD_Defs
import Definitions.Def_ModernOnlineLearning_Reductions_Setting

open ModernOnlineLearning.Reductions

theorem Orabona2019.theorem_12_5_faithful {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (V W : Set E) (hV : V.Nonempty)
    (hclosed : IsClosed V) (hconv : Convex ℝ V) (hVW : V ⊆ W)
    (loss : ℕ → E → ℝ) (z x : ℕ → E) (g q : ℕ → E →L[ℝ] ℝ)
    (T : ℕ) (hT : 1 ≤ T) (hRun : IsProjectedRun V W loss z x g q T)
    (u : E) (hu : u ∈ V) :
    (∀ k : Fin 4, ModernOnlineLearning.OGD.regret loss x u T ≤ surrogateRegret k V z x g q u T) ∧
    (∀ k : Fin 4, ∀ t ∈ Finset.Icc 1 T, ∀ y ∈ W, ∀ g' : E →L[ℝ] ℝ,
      IsSubgradient (fun w => surrogate k V (g t) (q t) (x t) (z t) w) y g' →
        ‖g'‖ ≤ 2 * ‖g t‖) := by sorry
