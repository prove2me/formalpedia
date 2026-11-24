-- Prove2me | Theorems.Thm_GoodViews_infomin_optimal_representation
-- name    : GoodViews.infomin_optimal_representation
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T05:43:43.693417+00:00
-- url     : https://prove2.me/theorems/39d88a20-a8ea-4a40-9c48-31e1ba89fc17
-- title:
--   Proposition 3.1: InfoMin views yield optimal representations
-- statement:
--   Let the data $x$ and the label $y$ of a downstream task be finitely-valued random variables on a finite probability space. Let the optimal views be
--
--   $$(v_1^*,v_2^*)=\operatorname*{arg\,min}_{v_1,v_2}I(v_1;v_2)\quad\text{subject to}\quad I(v_1;y)=I(v_2;y)=I(x;y),$$
--
--   the minimum being over views $v_1=g_1(x)$, $v_2=g_2(x)$ created from the data with values in given finite view spaces $V_1$, $V_2$. Let $f_1$ and $f_2$ be minimal sufficient encoders for the contrastive task between $v_1^*$ and $v_2^*$. Then the representations $z_1^*=f_1(v_1^*)$ and $z_2^*=f_2(v_2^*)$ are optimal for the task (Definition 3): each is a minimal sufficient statistic of $x$ for $y$.
--
--   This is the InfoMin principle: the best views share as little information as possible while keeping all the task-relevant information.
--
--   **Formalization Note** The first sentence of the printed proposition, which says what the optimal views are, is encoded as the definition of optimal views. The theorem is its second sentence. Both $z_1^*$ and $z_2^*$ are covered by the conclusion.
-- source:
--   Tian, Sun, Poole, Krishnan, Schmid and Isola, What Makes for Good Views for Contrastive Learning?, arXiv:2005.10243v3 (2020), Section 3.2, Proposition 3.1, p. 4; proof in Appendix A, pp. 15-16

import Mathlib
import Definitions.Def_GoodViews_Basic

open Finset

namespace GoodViews

theorem infomin_optimal_representation {S X Y V₁ V₂ Z₁ Z₂ : Type} [Fintype S] [Fintype X]
    [Fintype Y] [Fintype V₁] [Fintype V₂] [Fintype Z₁] [Fintype Z₂]
    (P : S → ℝ) (hP : IsPMF P) (x : S → X) (y : S → Y) (g₁ : X → V₁) (g₂ : X → V₂)
    (hopt : IsOptimalViews P x y g₁ g₂) (f₁ : V₁ → Z₁) (f₂ : V₂ → Z₂)
    (hf₁ : IsMinimalSufficientEncoder P (g₁ ∘ x) (g₂ ∘ x) f₁)
    (hf₂ : IsMinimalSufficientEncoder P (g₂ ∘ x) (g₁ ∘ x) f₂) :
    IsOptimalRep P x y (f₁ ∘ g₁) ∧ IsOptimalRep P x y (f₂ ∘ g₂) := by sorry

end GoodViews
