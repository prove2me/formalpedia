-- Prove2me | Theorems.Thm_MartOT_Abs_lemma_5_6
-- name    : MartOT.Abs.lemma_5_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:20:08.259487+00:00
-- url     : https://prove2.me/theorems/49b91c86-8228-45aa-88da-88812c2b5749
-- title:
--   Lemma 5.6, p. 36 — a nonempty convex set of martingale plans, each concentrated on some Γ with |Γ_x| ≤ 2, is a singleton
-- statement:
--   Let $\mu,\nu$ be finite measures on $\mathbb R$ with finite first moments, in convex order $\mu\preceq_C\nu$, and let $\mathcal E$ be a nonempty convex set of martingale transport plans in $\Pi_M(\mu,\nu)$: with $\pi,\pi'\in\mathcal E$ and $t\in[0,1]$, also $t\pi+(1-t)\pi'\in\mathcal E$. Assume that every $\pi\in\mathcal E$ is concentrated on some set $\Gamma^\pi\subseteq\mathbb R^2$ with
--
--   $$|\Gamma^\pi_x|\le2\qquad\text{for every }x\in\mathbb R,\qquad \Gamma^\pi_x=\{y:(x,y)\in\Gamma^\pi\}.$$
--
--   Then $\mathcal E$ consists of a single point.
--
--   Applied to the set of optimal plans between $\bar\mu=\mu-\mu\wedge\nu$ and $\bar\nu=\nu-\mu\wedge\nu$, this gives the uniqueness of the optimizer in Theorem 7.4.
--
--   **Formalization Note** "Concentrated on $\Gamma$" is $\pi(\Gamma^c)=0$; no measurability of $\Gamma^\pi$ is assumed, as on the page. Mixtures use the nonnegative extended-real weights $\mathrm{ofReal}(t)$, $\mathrm{ofReal}(1-t)$. Cardinalities are in $\mathbb N\cup\{\infty\}$.
-- source:
--   arXiv:1208.1509v2, Lemma 5.6, p. 36

import Mathlib
import Definitions.Def_MartOT_Var_Setting

namespace MartOT.Abs

open MeasureTheory

theorem lemma_5_6 (μ ν : Measure ℝ) (hμν : MartOT.Var.ConvexLE μ ν) (E : Set (Measure (ℝ × ℝ)))
    (hE : ∀ π ∈ E, MartOT.Var.IsMartingalePlan μ ν π) (hne : E.Nonempty)
    (hconv : ∀ π ∈ E, ∀ π' ∈ E, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ENNReal.ofReal t • π + ENNReal.ofReal (1 - t) • π' ∈ E)
    (hfib : ∀ π ∈ E, ∃ Γ : Set (ℝ × ℝ), π Γᶜ = 0 ∧ ∀ x : ℝ, {y : ℝ | (x, y) ∈ Γ}.encard ≤ 2) :
    ∃ π : Measure (ℝ × ℝ), E = {π} := by sorry

end MartOT.Abs
