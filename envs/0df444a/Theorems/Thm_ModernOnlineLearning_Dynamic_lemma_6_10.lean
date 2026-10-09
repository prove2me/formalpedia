-- Prove2me | Theorems.Thm_ModernOnlineLearning_Dynamic_lemma_6_10
-- name    : ModernOnlineLearning.Dynamic.lemma_6_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T05:31:55.124675+00:00
-- url     : https://prove2.me/theorems/87e634ec-92ee-40e6-b3fa-b28bf14ba3a6
-- title:
--   Lemma 6.10, p. 67 — one-step OMD inequality chain
-- statement:
--   Let $V\subseteq X$ be a nonempty closed convex feasible set in a finite-dimensional real normed space. Let $\psi$ be closed, differentiable at the interior points used by OMD, and $\lambda$-strongly convex on $V\cap\operatorname{int}X$, with $\lambda>0$. For an OMD update with step $\eta_t>0$, a chosen subgradient $g_t$, and every $u\in V$, the inequality part of Lemma 6.10 is
--
--   $$
--   \eta_t(\ell_t(x_t)-\ell_t(u))\le\eta_t\langle g_t,x_t-u\rangle
--   \le B_\psi(u;x_t)-B_\psi(u;x_{t+1})-B_\psi(x_{t+1};x_t)+\eta_t\langle g_t,x_t-x_{t+1}\rangle
--   \le B_\psi(u;x_t)-B_\psi(u;x_{t+1})+\frac{\eta_t^2}{2\lambda}\lVert g_t\rVert_*^2.
--   $$
--
--   This is the per-round estimate used in the dynamic regret analysis.
--
--   **Formalization Note** This item states the inequality part for an already-defined run; it does not claim the lemma's separate existence and uniqueness result. The OMD run records the interior condition and the book's Algorithm 6.1 update. Relative subgradients on $V$ suffice for these comparisons. The book assumes "(6.5) or (6.6)" and derives $x_{t+1}\in\operatorname{int}X$; here that conclusion is taken directly as a clause of the run, as Theorem 14.2 does. The book's $\lambda$-strong convexity "in $V$" is assumed only on the convex set $V\cap\operatorname{int}X$, which contains every point the inequality chain uses, so this item is implied by the book's inequality.
-- source:
--   Orabona, arXiv:1912.13213v10, Lemma 6.10 (inequality part), p. 67 (PDF p. 79)

import Mathlib
import Definitions.Def_ModernOnlineLearning_Dynamic_Defs

namespace ModernOnlineLearning.Dynamic

/-- Lemma 6.10, p. 67, inequality part, for a well-defined OMD run.
The existence and uniqueness assertion is represented by the run predicate's
chosen argmin and is not part of this item. -/
theorem lemma_6_10
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (X V : Set E) (ψ : E → ℝ) (η : ℕ → ℝ) (ℓ : ℕ → E → ℝ)
    (x : ℕ → E) (g : ℕ → E →L[ℝ] ℝ) (T : ℕ) (lam : ℝ)
    (hVsub : V ⊆ X) (hVne : V.Nonempty) (hVclosed : IsClosed V)
    (hVconv : Convex ℝ V) (hXconv : Convex ℝ X)
    (hψclosed : ClosedRegularizerOn X ψ)
    (hψstrict : StrictConvexOn ℝ X ψ)
    (hψdiff : DifferentiableOn ℝ ψ (interior X))
    (hlam : 0 < lam) (hψstrong : StrongConvexOn (V ∩ interior X) lam ψ)
    (hrun : IsOMDRun X V ψ η ℓ x g T) :
    ∀ t ∈ Finset.Icc 1 T, ∀ u ∈ V,
      η t * (ℓ t (x t) - ℓ t u) ≤ η t * (g t) (x t - u) ∧
      η t * (g t) (x t - u) ≤
        BeckTeboulleMD.EMDA.bregman ψ u (x t) -
          BeckTeboulleMD.EMDA.bregman ψ u (x (t + 1)) -
          BeckTeboulleMD.EMDA.bregman ψ (x (t + 1)) (x t) +
          (η t) * (g t) (x t - x (t + 1)) ∧
      BeckTeboulleMD.EMDA.bregman ψ u (x t) -
          BeckTeboulleMD.EMDA.bregman ψ u (x (t + 1)) -
          BeckTeboulleMD.EMDA.bregman ψ (x (t + 1)) (x t) +
          (η t) * (g t) (x t - x (t + 1)) ≤
        BeckTeboulleMD.EMDA.bregman ψ u (x t) -
          BeckTeboulleMD.EMDA.bregman ψ u (x (t + 1)) +
          ((η t) ^ 2 / (2 * lam)) * ‖g t‖ ^ 2 := by sorry

end ModernOnlineLearning.Dynamic
