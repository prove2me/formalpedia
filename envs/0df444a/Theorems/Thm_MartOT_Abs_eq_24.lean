-- Prove2me | Theorems.Thm_MartOT_Abs_eq_24
-- name    : MartOT.Abs.eq_24
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:19:24.83499+00:00
-- url     : https://prove2.me/theorems/06f3e384-661f-4997-93de-eb77d722bed5
-- title:
--   (24), proof of Theorem 7.4, p. 45 — on a finitely optimal Γ for c = |y − x|, no x′ < x ≤ y′, no y′ ≤ x < x′, no x′ ∉ [y⁻, y⁺]
-- statement:
--   Consider the cost $c(x,y)=|y-x|$ and a set $\Gamma\subseteq\mathbb R^2$ on which no finitely supported measure can be improved by a competitor (the property that Lemma 1.11 gives for an optimal plan). Let $(x,y^-),(x,y^+),(x',y')\in\Gamma$ with
--
--   $$y^-<y'<y^+\qquad\text{and}\qquad y^-<x<y^+ .$$
--
--   Then none of the configurations
--
--   $$x'<x\le y',\qquad y'\le x<x',\qquad x'\notin[y^-,y^+]$$
--
--   occurs.
--
--   These are the forbidden configurations (24) of the paper. The third one with $x'\ne x=y'$ says that mass sitting at $x$ cannot leave $x$ while other mass arrives at $x$ from elsewhere; this is what forces an optimal plan to keep $\mu\wedge\nu$ in place.
--
--   **Formalization Note** The hypothesis on $\Gamma$ is the conclusion of Lemma 1.11 for the cost $c(x,y)=|y-x|$: for every finitely supported $\alpha=\sum_{s\in S}w_s\delta_s$ with $S\subseteq\Gamma$ finite and $w_s\ge0$, and every competitor $\alpha'$ of $\alpha$, $\int c\,d\alpha\le\int c\,d\alpha'$. We call such a $\Gamma$ **finitely optimal** (the paper's Definition A.1, p. 46). The statement is about any such $\Gamma$, so it does not mention $\mu$, $\nu$ or the plan. The hypothesis $y^-<x<y^+$ is not in the sentence of p. 45 but is the hypothesis "$y^-<x,y'<y^+$" of Lemma 7.5, which the page invokes to conclude; without it the claim is false (for $\Gamma=\{(0,1),(0,2),(-1,3/2)\}$ every competitor has the same cost, because $|y-x|=y-x$ on $\Gamma$, yet $x'=-1<x=0\le y'=3/2$). Both applications of (24) in the proof of Theorem 7.4 (p. 46) have $x\in\,]y^-,y^+[$.
-- source:
--   arXiv:1208.1509v2, proof of Theorem 7.4, p. 45, display (24)

import Mathlib
import Definitions.Def_MartOT_Var_Setting

namespace MartOT.Abs

open MeasureTheory

theorem eq_24 (Γ : Set (ℝ × ℝ))
    (hΓ : ∀ (S : Finset (ℝ × ℝ)) (w : ℝ × ℝ → NNReal), (↑S : Set (ℝ × ℝ)) ⊆ Γ →
      ∀ α' : Measure (ℝ × ℝ),
        MartOT.Var.IsCompetitor (∑ p ∈ S, (w p : ENNReal) • Measure.dirac p) α' →
        MartOT.Var.cost (fun x y => |y - x|) (∑ p ∈ S, (w p : ENNReal) • Measure.dirac p) ≤
          MartOT.Var.cost (fun x y => |y - x|) α')
    (x ym yp x' y' : ℝ) (hm : (x, ym) ∈ Γ) (hp : (x, yp) ∈ Γ) (h' : (x', y') ∈ Γ)
    (hy : ym < y' ∧ y' < yp) (hx : ym < x ∧ x < yp) :
    ¬ (x' < x ∧ x ≤ y') ∧ ¬ (y' ≤ x ∧ x < x') ∧ ¬ (x' ∉ Set.Icc ym yp) := by sorry

end MartOT.Abs
