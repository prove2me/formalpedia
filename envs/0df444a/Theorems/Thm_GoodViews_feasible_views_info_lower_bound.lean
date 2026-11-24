-- Prove2me | Theorems.Thm_GoodViews_feasible_views_info_lower_bound
-- name    : GoodViews.feasible_views_info_lower_bound
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T05:39:56.795121+00:00
-- url     : https://prove2.me/theorems/557b75a4-affd-43e9-a4b6-3e1089be10bf
-- title:
--   Proposition A.1 (as proved): feasible views share at least $I(x;y)$, with equality iff they are conditionally independent given $y$
-- statement:
--   Let $x$ be the data and $y$ the task label, finitely-valued random variables on a finite probability space. Let $v_1=g_1(x)$ and $v_2=g_2(x)$ be views created from the data that keep all task information:
--
--   $$I(v_1;y)=I(v_2;y)=I(x;y).$$
--
--   Then:
--
--   1. $I(y;v_2\mid v_1)=0$;
--   2. $I(v_1;v_2)=I(x;y)+I(v_2;v_1\mid y)$;
--   3. $I(v_1;v_2)\ge I(x;y)$;
--   4. $I(v_1;v_2)=I(x;y)$ if and only if $I(v_2;v_1\mid y)=0$, i.e. the views are conditionally independent given $y$.
--
--   So views that reach the lower bound $I(x;y)$ are exactly the feasible views that are conditionally independent given the label.
--
--   **Formalization Note** This is what the proof of Proposition A.1 establishes. The printed statement asserts that the optimal views (the minimisers of $I(v_1;v_2)$ under the constraint) satisfy $I(v_1^*;v_2^*)=I(x;y)$ and are conditionally independent given $y$. That requires the lower bound to be attained, which the proof does not show and which can fail: the minimum over feasible views equals $H(T)$, where $T$ is the posterior class $x\mapsto p(y\mid x)$, and this equals $I(x;y)$ only when $H(T\mid y)=0$. For example, for $x$ uniform on $\{0,1\}$ and $y=x$ with probability $0.9$, every feasible view is injective, so $I(v_1^*;v_2^*)=\log2>I(x;y)$.
-- source:
--   Tian, Sun, Poole, Krishnan, Schmid and Isola, What Makes for Good Views for Contrastive Learning?, arXiv:2005.10243v3 (2020), Appendix A.2, Proposition A.1 and its proof, p. 15

import Mathlib
import Definitions.Def_GoodViews_Basic

open Finset

namespace GoodViews

theorem feasible_views_info_lower_bound {S X Y V₁ V₂ : Type} [Fintype S] [Fintype X]
    [Fintype Y] [Fintype V₁] [Fintype V₂] (P : S → ℝ) (hP : IsPMF P) (x : S → X) (y : S → Y)
    (g₁ : X → V₁) (g₂ : X → V₂) (hfeas : IsFeasibleViews P x y g₁ g₂) :
    condMutualInfo P y (g₂ ∘ x) (g₁ ∘ x) = 0 ∧
    mutualInfo P (g₁ ∘ x) (g₂ ∘ x) = mutualInfo P x y + condMutualInfo P (g₂ ∘ x) (g₁ ∘ x) y ∧
    mutualInfo P x y ≤ mutualInfo P (g₁ ∘ x) (g₂ ∘ x) ∧
    (mutualInfo P (g₁ ∘ x) (g₂ ∘ x) = mutualInfo P x y ↔
      condMutualInfo P (g₂ ∘ x) (g₁ ∘ x) y = 0) := by sorry

end GoodViews
