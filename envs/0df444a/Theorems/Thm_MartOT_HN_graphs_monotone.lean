-- Prove2me | Theorems.Thm_MartOT_HN_graphs_monotone
-- name    : MartOT.HN.graphs_monotone
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:19:54.709861+00:00
-- url     : https://prove2.me/theorems/1f6d015c-e8f4-447c-9e0f-31459ff79e25
-- title:
--   Proof of Theorem 7.3, p. 45 — on a finitely optimal Γ for c = −|y − x|, maps T₁ ≤ id ≤ T₂ with graphs in Γ are nondecreasing
-- statement:
--   Let $c(x,y)=-|y-x|$ and let $\Gamma\subseteq\mathbb R^2$ be a set on which no finitely supported measure is improved by a competitor. Let $S\subseteq\mathbb R$ and $T_1,T_2$ be real functions such that, for every $x\in S$, $(x,T_1(x))\in\Gamma$, $(x,T_2(x))\in\Gamma$ and
--
--   $$T_1(x)\le x\le T_2(x).$$
--
--   Then $T_1$ and $T_2$ are nondecreasing on $S$.
--
--   This is the monotonicity step of Theorem 7.3: the two maps describing an optimal plan for $-|y-x|$ are nondecreasing.
--
--   **Formalization Note** The hypothesis on $\Gamma$ is the conclusion of Lemma 1.11 for the cost $c(x,y)=-|y-x|$: for every finitely supported $\alpha=\sum_{s\in S}w_s\delta_s$ with $S\subseteq\Gamma$ finite and $w_s\ge0$, and every competitor $\alpha'$ of $\alpha$, $\int c\,d\alpha\le\int c\,d\alpha'$. We call such a $\Gamma$ **finitely optimal**. The page assumes $\Gamma_x=\{T_1(x),T_2(x)\}$; only the inclusion $\{T_1(x),T_2(x)\}\subseteq\Gamma_x$ is assumed here, which makes the statement stronger. The page's "for $\mu$-almost every $x$" is built into the choice of $S$.
-- source:
--   arXiv:1208.1509v2, proof of Theorem 7.3, p. 45 (second paragraph)

import Mathlib
import Definitions.Def_MartOT_Var_Setting

namespace MartOT.HN

open MeasureTheory

theorem graphs_monotone (Γ : Set (ℝ × ℝ))
    (hΓ : ∀ (S : Finset (ℝ × ℝ)) (w : ℝ × ℝ → NNReal), (↑S : Set (ℝ × ℝ)) ⊆ Γ →
      ∀ α' : Measure (ℝ × ℝ),
        MartOT.Var.IsCompetitor (∑ p ∈ S, (w p : ENNReal) • Measure.dirac p) α' →
        MartOT.Var.cost (fun x y => -|y - x|) (∑ p ∈ S, (w p : ENNReal) • Measure.dirac p) ≤
          MartOT.Var.cost (fun x y => -|y - x|) α')
    (S : Set ℝ) (T₁ T₂ : ℝ → ℝ) (h₁ : ∀ x ∈ S, (x, T₁ x) ∈ Γ) (h₂ : ∀ x ∈ S, (x, T₂ x) ∈ Γ)
    (hT : ∀ x ∈ S, T₁ x ≤ x ∧ x ≤ T₂ x) :
    MonotoneOn T₁ S ∧ MonotoneOn T₂ S := by sorry

end MartOT.HN
