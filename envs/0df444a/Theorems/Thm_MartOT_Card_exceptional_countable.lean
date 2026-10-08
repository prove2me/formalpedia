-- Prove2me | Theorems.Thm_MartOT_Card_exceptional_countable
-- name    : MartOT.Card.exceptional_countable
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:20:25.117886+00:00
-- url     : https://prove2.me/theorems/7c89c443-48e1-45f7-8815-35e4f3e4bffb
-- title:
--   Proof of Theorem 7.1, pp. 38–39 — on the Γ of Lemma 1.11 only countably many continuity points x of µ have card(Γ_x) ≥ k + 1
-- statement:
--   Let $\mu$ be a measure on $\mathbb R$, $h:\mathbb R\to\mathbb R$ twice continuously differentiable, $c(x,y)=h(y-x)$, and assume that every affine function meets $h'$ in at most $k$ points. Let $\Gamma\subseteq\mathbb R^2$ have the property that Lemma 1.11 provides: for every finitely supported finite measure $\alpha$ with $\operatorname{spt}\alpha\subseteq\Gamma$,
--   $$\int c\,d\alpha\le\int c\,d\alpha'\qquad\text{for every competitor }\alpha'\text{ of }\alpha .$$
--   Then the set of continuity points of $\mu$ whose fibre has at least $k+1$ points,
--   $$\big\{x\in\mathbb R:\ \mu(\{x\})=0,\ |\Gamma_x|\ge k+1\big\},\qquad \Gamma_x=\{y:(x,y)\in\Gamma\},$$
--   is countable.
--
--   This is the core of Theorem 7.1: these countably many $\mu$-null fibres can be removed from $\Gamma$, after which every non-atom $x$ carries at most $k$ points.
--
--   **Formalization Note** The finitely supported $\alpha$ are written $\sum_{s\in S}w_s\delta_s$ with $S$ finite and $w_s\ge0$, as in Lemma 1.11, and costs are extended-real integrals. The property of $\Gamma$ is carried as a hypothesis instead of deriving $\Gamma$ from Lemma 1.11, so $\nu$, $\pi$, the convex order, optimality, $\pi(\Gamma)=1$ and Borel measurability of $\Gamma$ are not needed and are dropped; this makes the statement more general. The cardinality $|\Gamma_x|$ is taken in $\mathbb N\cup\{\infty\}$.
-- source:
--   arXiv:1208.1509v2, §7.1, proof of Theorem 7.1, pp. 38–39 (first paragraph of the proof)

import Mathlib
import Definitions.Def_MartOT_Var_Setting

namespace MartOT.Card

open MeasureTheory

/-- Proof of Theorem 7.1, pp. 38–39: if `Γ` has the conclusion property of Lemma 1.11 for the MartOT.Var.cost
`c(x, y) = h(y − x)`, then only countably many continuity points `x` of `μ` have `card(Γ_x) ≥ k + 1`. -/
theorem exceptional_countable (μ : Measure ℝ) (h : ℝ → ℝ) (hh : ContDiff ℝ 2 h) (k : ℕ)
    (hk : ∀ s t : ℝ, {x : ℝ | deriv h x = s * x + t}.encard ≤ k)
    (Γ : Set (ℝ × ℝ))
    (hΓ : ∀ (S : Finset (ℝ × ℝ)) (w : ℝ × ℝ → NNReal), (↑S : Set (ℝ × ℝ)) ⊆ Γ →
        ∀ α' : Measure (ℝ × ℝ),
          MartOT.Var.IsCompetitor (∑ p ∈ S, (w p : ENNReal) • Measure.dirac p) α' →
          MartOT.Var.cost (fun x y => h (y - x)) (∑ p ∈ S, (w p : ENNReal) • Measure.dirac p) ≤
            MartOT.Var.cost (fun x y => h (y - x)) α') :
    {x : ℝ | μ {x} = 0 ∧ ((k + 1 : ℕ) : ℕ∞) ≤ {y : ℝ | (x, y) ∈ Γ}.encard}.Countable := by sorry

end MartOT.Card
