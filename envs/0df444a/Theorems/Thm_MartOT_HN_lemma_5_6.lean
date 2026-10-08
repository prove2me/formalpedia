-- Prove2me | Theorems.Thm_MartOT_HN_lemma_5_6
-- name    : MartOT.HN.lemma_5_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:19:56.795722+00:00
-- url     : https://prove2.me/theorems/2d0f46f5-1a96-45ab-8c07-03401a8e92cd
-- title:
--   Lemma 5.6, p. 36 — a nonempty convex set of martingale plans, each on a set with |Γ_x| ≤ 2, is a single point
-- statement:
--   Let $\mu$ and $\nu$ be finite measures on $\mathbb R$ in convex order, and let $\mathcal E$ be a nonempty convex set of martingale transport plans from $\mu$ to $\nu$. Assume that every $\pi\in\mathcal E$ is concentrated on some set $\Gamma^\pi\subseteq\mathbb R^2$ with $|\Gamma^\pi_x|\le2$ for every $x\in\mathbb R$. Then
--
--   $$\mathcal E=\{\pi\}\quad\text{for a single plan }\pi.$$
--
--   Together with the convexity of the set of optimizers, this turns "every optimizer lives on two graphs" into "the optimizer is unique".
--
--   **Formalization Note** Convexity of $\mathcal E$ is closure under $\mathrm{ofReal}(t)\,\pi+\mathrm{ofReal}(1-t)\,\pi'$, $t\in[0,1]$. "Concentrated on $\Gamma$" is $\pi(\Gamma^c)=0$; $\Gamma^\pi$ is not assumed measurable, as on the page. The convex order of Definition 2.1 makes $\mu,\nu$ finite with finite first moments.
-- source:
--   arXiv:1208.1509v2, Lemma 5.6, p. 36

import Mathlib
import Definitions.Def_MartOT_Var_Setting

namespace MartOT.HN

open MeasureTheory

theorem lemma_5_6 (μ ν : Measure ℝ) (hμν : MartOT.Var.ConvexLE μ ν) (E : Set (Measure (ℝ × ℝ)))
    (hE : ∀ π ∈ E, MartOT.Var.IsMartingalePlan μ ν π) (hne : E.Nonempty)
    (hconv : ∀ π ∈ E, ∀ π' ∈ E, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ENNReal.ofReal t • π + ENNReal.ofReal (1 - t) • π' ∈ E)
    (hfib : ∀ π ∈ E, ∃ Γ : Set (ℝ × ℝ), π Γᶜ = 0 ∧ ∀ x : ℝ, {y : ℝ | (x, y) ∈ Γ}.encard ≤ 2) :
    ∃ π : Measure (ℝ × ℝ), E = {π} := by sorry

end MartOT.HN
