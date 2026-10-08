-- Prove2me | Theorems.Thm_MartOT_Abs_lemma_5_5
-- name    : MartOT.Abs.lemma_5_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:20:11.517446+00:00
-- url     : https://prove2.me/theorems/fb3f3557-3a43-41ef-83ad-4799037e94ee
-- title:
--   Lemma 5.5, p. 35 — a Borel Γ ⊆ ℝ² with |Γ_x| ≤ 2 has Borel projection and is the union of two Borel graphs T₁ ≤ T₂
-- statement:
--   Let $\Gamma\subseteq\mathbb R^2$ be a Borel set such that $|\Gamma_x|\le2$ for every $x\in\mathbb R$, where $\Gamma_x=\{y:(x,y)\in\Gamma\}$. Then $S=\operatorname{proj}^x(\Gamma)$ is a Borel set, and there are Borel functions $T_1,T_2:S\to\mathbb R$ with $T_1\le T_2$ such that
--
--   $$\Gamma=\operatorname{graph}(T_1)\cup\operatorname{graph}(T_2).$$
--
--   The paper cites this as a consequence of Kechris, *Classical Descriptive Set Theory*, Theorem 18.11 (Lusin–Novikov). It turns a set with at most two points per fibre into two measurable maps.
--
--   **Formalization Note** $T_1,T_2$ are written as Borel functions on all of $\mathbb R$, of which only the values on $S$ matter; since $S$ is Borel, a Borel function on $S$ extends to a Borel function on $\mathbb R$, so this is equivalent. $\operatorname{graph}(T_i)=\{(x,T_i(x)):x\in S\}$.
-- source:
--   arXiv:1208.1509v2, Lemma 5.5, p. 35

import Mathlib
import Definitions.Def_MartOT_Var_Setting

namespace MartOT.Abs

open MeasureTheory

theorem lemma_5_5 (Γ : Set (ℝ × ℝ)) (hΓ : MeasurableSet Γ)
    (h2 : ∀ x : ℝ, {y : ℝ | (x, y) ∈ Γ}.encard ≤ 2) :
    MeasurableSet (Prod.fst '' Γ) ∧
      ∃ T₁ T₂ : ℝ → ℝ, Measurable T₁ ∧ Measurable T₂ ∧
        (∀ x ∈ Prod.fst '' Γ, T₁ x ≤ T₂ x) ∧
        Γ = {p : ℝ × ℝ | p.1 ∈ Prod.fst '' Γ ∧ (p.2 = T₁ p.1 ∨ p.2 = T₂ p.1)} := by sorry

end MartOT.Abs
