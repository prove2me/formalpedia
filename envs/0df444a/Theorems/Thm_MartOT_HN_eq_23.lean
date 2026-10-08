-- Prove2me | Theorems.Thm_MartOT_HN_eq_23
-- name    : MartOT.HN.eq_23
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:19:15.682984+00:00
-- url     : https://prove2.me/theorems/79c037b2-4d8f-4c9e-97f3-61e1aac6b189
-- title:
--   (23), proof of Theorem 7.3, p. 44 — on a finitely optimal Γ for c = −|y − x|, no y′ ≤ x′ < x and no x < x′ ≤ y′
-- statement:
--   Consider the Hobson–Neuberger cost $c(x,y)=-|y-x|$ and a set $\Gamma\subseteq\mathbb R^2$ on which no finitely supported measure can be improved by a competitor (the property that Lemma 1.11 gives for an optimal plan). Let $(x,y^-),(x,y^+),(x',y')\in\Gamma$ with $y^-<y'<y^+$. Then neither of the configurations
--
--   $$y'\le x'<x\qquad\text{or}\qquad x<x'\le y'$$
--
--   occurs.
--
--   These are the forbidden configurations (23) of the paper; they force optimal plans for $-|y-x|$ onto two monotone graphs.
--
--   **Formalization Note** The hypothesis on $\Gamma$ is the conclusion of Lemma 1.11 for the cost $c(x,y)=-|y-x|$: for every finitely supported $\alpha=\sum_{s\in S}w_s\delta_s$ with $S\subseteq\Gamma$ finite and $w_s\ge0$, and every competitor $\alpha'$ of $\alpha$, $\int c\,d\alpha\le\int c\,d\alpha'$. We call such a $\Gamma$ **finitely optimal**. The statement is about any such $\Gamma$, so it does not mention $\mu$, $\nu$ or the plan.
-- source:
--   arXiv:1208.1509v2, proof of Theorem 7.3, p. 44, display (23)

import Mathlib
import Definitions.Def_MartOT_Var_Setting

namespace MartOT.HN

open MeasureTheory

theorem eq_23 (Γ : Set (ℝ × ℝ))
    (hΓ : ∀ (S : Finset (ℝ × ℝ)) (w : ℝ × ℝ → NNReal), (↑S : Set (ℝ × ℝ)) ⊆ Γ →
      ∀ α' : Measure (ℝ × ℝ),
        MartOT.Var.IsCompetitor (∑ p ∈ S, (w p : ENNReal) • Measure.dirac p) α' →
        MartOT.Var.cost (fun x y => -|y - x|) (∑ p ∈ S, (w p : ENNReal) • Measure.dirac p) ≤
          MartOT.Var.cost (fun x y => -|y - x|) α')
    (x ym yp x' y' : ℝ) (hm : (x, ym) ∈ Γ) (hp : (x, yp) ∈ Γ) (h' : (x', y') ∈ Γ)
    (hy : ym < y' ∧ y' < yp) :
    ¬ (y' ≤ x' ∧ x' < x) ∧ ¬ (x < x' ∧ x' ≤ y') := by sorry

end MartOT.HN
