-- Prove2me | Theorems.Thm_MartOT_HN_fibres_le_two_straddle
-- name    : MartOT.HN.fibres_le_two_straddle
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-11-05T05:51:50.032913+00:00
-- url     : https://prove2.me/theorems/45b4a088-b6c0-422e-991b-de478018324e
-- title:
--   Proof of Theorem 7.3, p. 45 — with straddling fibres, the set of a with |Γ_a| > 2 is countable, hence µ-null
-- statement:
--   Let $\mu$ be a measure on $\mathbb R$ without atoms ($\mu(\{x\})=0$ for every $x$). Let $\Gamma\subseteq\mathbb R^2$ have the variational property of Lemma 1.11 for $c(x,y)=-|y-x|$: for every finitely supported measure $\alpha$ with $\operatorname{spt}\alpha\subseteq\Gamma$ and every competitor $\alpha'$ of $\alpha$,
--
--   $$\int c\,d\alpha\le\int c\,d\alpha'.$$
--
--   Assume moreover that every nonempty fibre straddles its base point: whenever $\Gamma_a=\{y:(a,y)\in\Gamma\}\neq\emptyset$, there are $y_1,y_2\in\Gamma_a$ with $y_1\le a\le y_2$. Then the set
--
--   $$A=\{a\in\mathbb R:\ |\Gamma_a|>2\}$$
--
--   is countable, and hence $\mu(A)=0$.
--
--   This is the first paragraph of the proof of Theorem 7.3 (p. 45), with the straddling hypothesis stated explicitly. In the paper it comes from the martingale property: for $\mu$-a.e. $x$, $\Gamma_x$ has points on both sides of $x$. The paper's "without loss of generality $b\le a$ … $a<a_0<b_0^+$" step needs it. Without it the claim is false: `MartOT.HN.fibres_le_two`, which keeps only the variational property, is disproved by $\Gamma=[0,1]\times\{-1,-2,-3\}$.
-- source:
--   Beiglböck–Juillet, On a problem of optimal transport under marginal martingale constraints, arXiv:1208.1509v2, proof of Theorem 7.3, p. 45 (first paragraph), using (23) and Lemma 3.2

import Mathlib
import Definitions.Def_MartOT_Var_Setting

namespace MartOT.HN

open MeasureTheory

theorem fibres_le_two_straddle (μ : Measure ℝ) (hμc : ∀ x : ℝ, μ {x} = 0) (Γ : Set (ℝ × ℝ))
    (hΓ : ∀ (S : Finset (ℝ × ℝ)) (w : ℝ × ℝ → NNReal), (↑S : Set (ℝ × ℝ)) ⊆ Γ →
      ∀ α' : Measure (ℝ × ℝ),
        MartOT.Var.IsCompetitor (∑ p ∈ S, (w p : ENNReal) • Measure.dirac p) α' →
        MartOT.Var.cost (fun x y => -|y - x|) (∑ p ∈ S, (w p : ENNReal) • Measure.dirac p) ≤
          MartOT.Var.cost (fun x y => -|y - x|) α')
    (hstr : ∀ a y : ℝ, (a, y) ∈ Γ →
      (∃ y₁ : ℝ, (a, y₁) ∈ Γ ∧ y₁ ≤ a) ∧ (∃ y₂ : ℝ, (a, y₂) ∈ Γ ∧ a ≤ y₂)) :
    {a : ℝ | 2 < {y : ℝ | (a, y) ∈ Γ}.encard}.Countable ∧
      μ {a : ℝ | 2 < {y : ℝ | (a, y) ∈ Γ}.encard} = 0 := by sorry

end MartOT.HN
