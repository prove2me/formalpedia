-- Prove2me | Theorems.Thm_MartOT_HN_fibres_le_two
-- name    : MartOT.HN.fibres_le_two
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:19:44.731128+00:00
-- url     : https://prove2.me/theorems/90417c38-52d7-40db-bc80-1373f8481df2
-- title:
--   Proof of Theorem 7.3, p. 45 — on a finitely optimal Γ for c = −|y − x|, the set of a with |Γ_a| > 2 is countable, hence µ-null
-- statement:
--   Let $c(x,y)=-|y-x|$ and let $\Gamma\subseteq\mathbb R^2$ be a set on which no finitely supported measure is improved by a competitor. Let $\mu$ be a continuous measure on $\mathbb R$, that is, $\mu(\{x\})=0$ for every $x$. Then the set
--
--   $$A=\{a\in\mathbb R:\ |\Gamma_a|>2\},\qquad \Gamma_a=\{y:(a,y)\in\Gamma\},$$
--
--   is countable, and therefore $\mu(A)=0$.
--
--   After discarding $A\times\mathbb R$, every fibre of $\Gamma$ has at most two points, which is where the two maps $T_1,T_2$ of Theorem 7.3 come from.
--
--   **Formalization Note** The hypothesis on $\Gamma$ is the conclusion of Lemma 1.11 for the cost $c(x,y)=-|y-x|$: for every finitely supported $\alpha=\sum_{s\in S}w_s\delta_s$ with $S\subseteq\Gamma$ finite and $w_s\ge0$, and every competitor $\alpha'$ of $\alpha$, $\int c\,d\alpha\le\int c\,d\alpha'$. We call such a $\Gamma$ **finitely optimal**. Continuity of $\mu$ is the hypothesis $\mu(\{x\})=0$ for every $x$; $\mu$ is otherwise arbitrary. Cardinalities are in $\mathbb N\cup\{\infty\}$.
-- source:
--   arXiv:1208.1509v2, proof of Theorem 7.3, p. 45 (first paragraph)

import Mathlib
import Definitions.Def_MartOT_Var_Setting

namespace MartOT.HN

open MeasureTheory

theorem fibres_le_two (μ : Measure ℝ) (hμc : ∀ x : ℝ, μ {x} = 0) (Γ : Set (ℝ × ℝ))
    (hΓ : ∀ (S : Finset (ℝ × ℝ)) (w : ℝ × ℝ → NNReal), (↑S : Set (ℝ × ℝ)) ⊆ Γ →
      ∀ α' : Measure (ℝ × ℝ),
        MartOT.Var.IsCompetitor (∑ p ∈ S, (w p : ENNReal) • Measure.dirac p) α' →
        MartOT.Var.cost (fun x y => -|y - x|) (∑ p ∈ S, (w p : ENNReal) • Measure.dirac p) ≤
          MartOT.Var.cost (fun x y => -|y - x|) α') :
    {a : ℝ | 2 < {y : ℝ | (a, y) ∈ Γ}.encard}.Countable ∧
      μ {a : ℝ | 2 < {y : ℝ | (a, y) ∈ Γ}.encard} = 0 := by sorry

end MartOT.HN
