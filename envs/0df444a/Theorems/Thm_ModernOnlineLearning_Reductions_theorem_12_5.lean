-- Prove2me | Theorems.Thm_ModernOnlineLearning_Reductions_theorem_12_5
-- name    : ModernOnlineLearning.Reductions.theorem_12_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T05:32:43.509777+00:00
-- url     : https://prove2.me/theorems/36e953fa-061b-4989-82af-fab78b412f20
-- title:
--   Theorem 12.5 — four surrogate losses dominate constrained regret
-- statement:
--   Let $V\subseteq W$ with $V$ nonempty, closed, and convex. On each of rounds $1,\ldots,T$, let $z_t\in W$, choose any $x_t\in\Pi_V(z_t)$, let $g_t$ be a subgradient of $\ell_t$ at $x_t$ for comparison with points of $V$, and choose $q_t\in\partial d_V(z_t)$. For each of the four surrogate losses $\widetilde\ell_t^{(k)}$ listed in the theorem, and every $u\in V$,
--   $$\operatorname{Regret}_T(u)=\sum_{t=1}^{T}(\ell_t(x_t)-\ell_t(u))\le\sum_{t=1}^{T}\bigl(\widetilde\ell_t^{(k)}(z_t)-\widetilde\ell_t^{(k)}(u)\bigr),\qquad k=1,2,3,4.$$
--   Thus any unconstrained learner's regret bound on one of these surrogate sequences transfers to its projected predictions on $V$.
--
--   **Formalization Note** The four choices are indexed $0,1,2,3$ in Lean, in the book's order. The learner is represented by its arbitrary prediction sequence $z_t$; the inequality is pathwise. The loss subgradient condition is relative to $V$, and $T\ge1$ makes the book's one-based horizon explicit.
-- source:
--   Orabona, arXiv:1912.13213v10, Theorem 12.5, pp. 195–196

import Mathlib
import Definitions.Def_ModernOnlineLearning_Reductions_Setting

namespace ModernOnlineLearning.Reductions

/-- Orabona, Theorem 12.5, pp. 195–196: each of the four printed surrogate choices
dominates the constrained ModernOnlineLearning.OGD.regret on every projected run. -/
theorem theorem_12_5 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (V W : Set E) (hV : V.Nonempty)
    (hclosed : IsClosed V) (hconv : Convex ℝ V) (hVW : V ⊆ W)
    (loss : ℕ → E → ℝ) (z x : ℕ → E) (g q : ℕ → E →L[ℝ] ℝ)
    (T : ℕ) (hT : 1 ≤ T) (hRun : IsProjectedRun V W loss z x g q T)
    (u : E) (hu : u ∈ V) :
    ∀ k : Fin 4, ModernOnlineLearning.OGD.regret loss x u T ≤ surrogateRegret k V z x g q u T := by sorry

end ModernOnlineLearning.Reductions
