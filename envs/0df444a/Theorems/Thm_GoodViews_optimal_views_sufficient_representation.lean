-- Prove2me | Theorems.Thm_GoodViews_optimal_views_sufficient_representation
-- name    : GoodViews.optimal_views_sufficient_representation
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-24T05:40:27.981808+00:00
-- url     : https://prove2.me/theorems/8ff884ad-b00c-4764-8150-d844c8c4f013
-- title:
--   Proposition A.2: with optimal views, minimal sufficient encoders give sufficient statistics for $y$
-- statement:
--   Let $x$ be the data and $y$ the task label, finitely-valued random variables on a finite probability space. Let $(v_1^*,v_2^*)=(g_1(x),g_2(x))$ be optimal views: among all pairs of views $g_1':X\to V_1$, $g_2':X\to V_2$ with $I(g_1'(x);y)=I(g_2'(x);y)=I(x;y)$, they minimise $I(g_1'(x);g_2'(x))$. Let $f_1$ and $f_2$ be minimal sufficient encoders of $v_1^*$ and $v_2^*$ (Definitions 1 and 2). Then the representations $z_1=f_1(v_1^*)$ and $z_2=f_2(v_2^*)$ are sufficient statistics of $v_1^*$ and $v_2^*$ for $y$:
--
--   $$I(z_1;y)=I(v_1^*;y),\qquad I(z_2;y)=I(v_2^*;y).$$
--
--   Together with Proposition A.3 this shows that contrastive learning with optimal views loses no task information.
--
--   **Formalization Note** The paper writes "$z_1$ (or $z_2$)"; both conclusions are stated. Sufficiency of $f_2$ is written as $I(v_2;v_1)=I(f_2(v_2);v_1)$, which equals the paper's $I(v_1;v_2)=I(v_1;f_2(v_2))$ by symmetry of mutual information.
-- source:
--   Tian, Sun, Poole, Krishnan, Schmid and Isola, What Makes for Good Views for Contrastive Learning?, arXiv:2005.10243v3 (2020), Appendix A.2, Proposition A.2, pp. 15-16

import Mathlib
import Definitions.Def_GoodViews_Basic

open Finset

namespace GoodViews

theorem optimal_views_sufficient_representation {S X Y V₁ V₂ Z₁ Z₂ : Type} [Fintype S]
    [Fintype X] [Fintype Y] [Fintype V₁] [Fintype V₂] [Fintype Z₁] [Fintype Z₂]
    (P : S → ℝ) (hP : IsPMF P) (x : S → X) (y : S → Y) (g₁ : X → V₁) (g₂ : X → V₂)
    (hopt : IsOptimalViews P x y g₁ g₂) (f₁ : V₁ → Z₁) (f₂ : V₂ → Z₂)
    (hf₁ : IsMinimalSufficientEncoder P (g₁ ∘ x) (g₂ ∘ x) f₁)
    (hf₂ : IsMinimalSufficientEncoder P (g₂ ∘ x) (g₁ ∘ x) f₂) :
    IsSufficientStat P (g₁ ∘ x) y f₁ ∧ IsSufficientStat P (g₂ ∘ x) y f₂ := by sorry

end GoodViews
