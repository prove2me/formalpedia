-- Prove2me | Theorems.Thm_JEPAGeneralization_single_step_planning_regret
-- name    : JEPAGeneralization.single_step_planning_regret
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T04:43:04.61889+00:00
-- url     : https://prove2.me/theorems/680cc3c4-86bb-43b2-826b-4b1599c4ef28
-- title:
--   Theorem 4.1 (as proved): single-step planning
-- statement:
--   Let $w$ be an action-conditioned co-occurrence model on a finite observation space $\mathcal X$ with positive marginals and a finite nonempty action set $\mathcal A$. Let $\rho$ be a law of the initial and goal observations $(x_0,x_g)$, with $\mathbb E_\rho\,w(x_g\mid a)$ the same for all $a$. Let $(f,g)$ be normalized at every action. For each $(x_0,x_g)$, let $\tilde a(x_0,x_g)$ minimize the planning loss $\|g(f(x_0),a)-f(x_g)\|^2$ over $a$, and let $a^{**}(x_0,x_g)$ maximize the value $V(a)=w(x_0,x_g,a)/w(x_0)$. Then
--
--   $$\mathcal E(\tilde a)\le 2c_0\max_a\sqrt{\mathcal R_{\mathrm{S\text{-}JEPA}}(f,g,a)}+\mathbb E_\rho\Big[\big(w(x_g\mid a^{**})-w(x_g\mid\tilde a)\big)\,g(f(x_0),a^{**})^\top f(x_g)\Big],$$
--
--   where $c_0=\mathbb E_\rho\sqrt{\max_aw(x_g\mid a)/w(x_0)}$ and $\mathcal E(\tilde a)=\mathbb E_\rho\big[V(a^{**})-V(\tilde a)\big]$.
--
--   This bounds the regret of planning in latent space by the spectral pretraining risk plus a term that compares the goal marginals of the optimal and the planned action.
--
--   **Formalization Note** This is what the proof establishes (Appendix A.2, up to eq. (41)). The printed Theorem 4.1 has no second term, and it is false: there are examples that satisfy all its hypotheses with $\mathcal E(\tilde a)=0.4$ and right-hand side below $0.003$. The proof's last steps bound the second term by $w(x_g\mid a^{**})-w(x_g\mid\tilde a)$ and then take its expectation to be $0$. Both steps fail. The first fails because the bracket $w(x_g\mid a^{**})-w(x_g\mid\tilde a)$ can be negative while $g^\top f<1$. The second fails because $a^{**}$ and $\tilde a$ depend on $(x_g,x_0)$. The hypothesis $\mathbb E_\rho w(x_g\mid a)=\mathbb E_\rho w(x_g\mid a')$ is the paper's and is kept, although the stated conclusion does not need it. The normalization of $(f,g)$ is used by the proof in $\arg\min_a\|g-f\|^2=\arg\max_ag^\top f$ and is added. Ties in the arg min and arg max are allowed: the statement holds for every choice of minimizer and maximizer. The paper does not specify the law of $(x_0,x_g)$, so it is an arbitrary $\rho$.
-- source:
--   Cui, Zhang, Wen, Cheng and Wang, A Generalization Theory for JEPA-Based World Models, arXiv:2606.27014v2 (2026), Section 4.1, Theorem 4.1, eq. (15)-(16), p. 5; proof in Appendix A.2, eq. (33)-(41), pp. 13-14

import Mathlib
import Definitions.Def_JEPAGeneralization_Basic

open Finset

namespace JEPAGeneralization

theorem single_step_planning_regret {X A : Type*} [Fintype X] [Fintype A] [Nonempty A] {k : ℕ}
    (pX : X → ℝ) (w : X → X → A → ℝ) (hw : IsCoOccurrence pX w)
    (ρ : X → X → ℝ) (hρ : IsPairDist ρ)
    (hgoal : ∀ a a' : A, ∑ x0, ∑ xg, ρ x0 xg * nextMarg w a xg = ∑ x0, ∑ xg, ρ x0 xg * nextMarg w a' xg)
    (f : X → Fin k → ℝ) (g : (Fin k → ℝ) → A → Fin k → ℝ) (hfg : ∀ a, IsNormalized f g a)
    (aT : X → X → A) (haT : ∀ x0 xg a, planLoss1 f g (aT x0 xg) x0 xg ≤ planLoss1 f g a x0 xg)
    (aS : X → X → A) (haS : ∀ x0 xg a, value1 pX w a x0 xg ≤ value1 pX w (aS x0 xg) x0 xg) :
    expRegret1 pX w ρ aT ≤
      2 * cZero pX w ρ * (⨆ a, Real.sqrt (sJepaRisk pX w f g a)) +
        ∑ x0, ∑ xg, ρ x0 xg * ((nextMarg w (aS x0 xg) xg - nextMarg w (aT x0 xg) xg) *
          dot (g (f x0) (aS x0 xg)) (f xg)) := by sorry

end JEPAGeneralization
