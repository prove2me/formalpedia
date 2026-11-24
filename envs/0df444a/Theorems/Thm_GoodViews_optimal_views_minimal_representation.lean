-- Prove2me | Theorems.Thm_GoodViews_optimal_views_minimal_representation
-- name    : GoodViews.optimal_views_minimal_representation
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T05:42:24.494151+00:00
-- url     : https://prove2.me/theorems/b99eabf1-a27a-4a1e-bbc2-ea4468ed76a1
-- title:
--   Proposition A.3: the representations are also minimal for $y$
-- statement:
--   In the setting of Proposition A.2, let $(v_1^*,v_2^*)=(g_1(x),g_2(x))$ be optimal views for the label $y$, and let $f_1$, $f_2$ be minimal sufficient encoders of $v_1^*$ and $v_2^*$. Then $z_1=f_1(v_1^*)$ is a minimal sufficient statistic of $v_1^*$ for $y$:
--
--   $$I(z_1;y)=I(v_1^*;y)\quad\text{and}\quad I(z_1;v_1^*)\le I(t(v_1^*);v_1^*)$$
--
--   for every function $t$ of $v_1^*$ into a finite set with $I(t(v_1^*);y)=I(v_1^*;y)$. The same holds for $z_2=f_2(v_2^*)$.
--
--   **Formalization Note** "Minimal for $y$" is read, as in the last line of the paper's proof, as "minimal sufficient statistic for predicting $y$", with minimality in the information form $I(z;v)\le I(t(v);v)$ used by the proof.
-- source:
--   Tian, Sun, Poole, Krishnan, Schmid and Isola, What Makes for Good Views for Contrastive Learning?, arXiv:2005.10243v3 (2020), Appendix A.2, Proposition A.3, p. 16

import Mathlib
import Definitions.Def_GoodViews_Basic

open Finset

namespace GoodViews

theorem optimal_views_minimal_representation {S X Y V₁ V₂ Z₁ Z₂ : Type} [Fintype S]
    [Fintype X] [Fintype Y] [Fintype V₁] [Fintype V₂] [Fintype Z₁] [Fintype Z₂]
    (P : S → ℝ) (hP : IsPMF P) (x : S → X) (y : S → Y) (g₁ : X → V₁) (g₂ : X → V₂)
    (hopt : IsOptimalViews P x y g₁ g₂) (f₁ : V₁ → Z₁) (f₂ : V₂ → Z₂)
    (hf₁ : IsMinimalSufficientEncoder P (g₁ ∘ x) (g₂ ∘ x) f₁)
    (hf₂ : IsMinimalSufficientEncoder P (g₂ ∘ x) (g₁ ∘ x) f₂) :
    IsMinimalSufficientStat P (g₁ ∘ x) y f₁ ∧ IsMinimalSufficientStat P (g₂ ∘ x) y f₂ := by sorry

end GoodViews
