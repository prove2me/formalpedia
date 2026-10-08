-- Prove2me | Theorems.Thm_MartOT_Shadow_example_4_7
-- name    : MartOT.Shadow.example_4_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:21:56.28716+00:00
-- url     : https://prove2.me/theorems/6ab440b7-8d0e-4dff-a8f8-a87d887f2990
-- title:
--   Example 4.7, p. 24 — the shadow of an atom is the restriction of ν between two quantiles
-- statement:
--   Let $\delta=\alpha\,\delta_x$ be an atom of mass $\alpha\ge0$ at a point $x\in\mathbb R$, and let $\nu$ be a finite Borel measure on $\mathbb R$ with finite first moment such that $\delta\preceq_E\nu$ (extended convex order). Let $G_\nu$ be the quantile function of $\nu$ and $\lambda$ the Lebesgue measure.
--
--   Then there are $0\le s\le s'\le\nu(\mathbb R)$ with $s'-s=\alpha$ such that the restriction of $\nu$ between the quantiles $s$ and $s'$,
--   $$\nu'=(G_\nu)_\#\lambda_{[s,s']},$$
--   has barycenter $x$, i.e. $\int y\,d\nu'(y)=\alpha x$, and $\nu'$ is the shadow $S^\nu(\delta)$ of $\delta$ in $\nu$.
--
--   This explicit description of the shadow of an atom is what the approximation of general measures by atomic ones (Lemmas 4.11–4.13) works with.
--
--   **Formalization Note** The barycenter condition is written as $\int y\,d\nu'=\alpha x$, which is "barycenter $x$" for $\alpha>0$ and trivially true for $\alpha=0$ (then $\nu'=0=\delta$). Shadows are encoded as the predicate `IsShadow ν μ η` (properties (i)–(iii) of Lemma 4.6), never as a chosen function; by Lemma 4.6 a shadow exists and is unique under the stated hypotheses, so quantifying over all $\eta$ with `IsShadow` is equivalent to speaking of $S^\nu(\mu)$. The subtraction $\nu-\eta$ is Mathlib's truncated subtraction of measures; it is the paper's difference whenever $\eta\le\nu$, which is guaranteed here by property (i) of the shadow.
-- source:
--   arXiv:1208.1509v2, Example 4.7, p. 24

import Mathlib
import Definitions.Def_MartOT_Var_Setting
import Definitions.Def_MartOT_Shadow_Quantile

namespace MartOT.Shadow

open MeasureTheory NNReal

theorem example_4_7 (α : ℝ≥0) (x : ℝ) (ν : Measure ℝ)
    (h : MartOT.Var.ExtConvexLE ((α : ENNReal) • Measure.dirac x) ν) :
    ∃ s s' : ℝ, 0 ≤ s ∧ s' ≤ (ν Set.univ).toReal ∧ s' - s = α ∧
      ∫ y, y ∂(quantileSlice ν s s') = α * x ∧
      MartOT.Var.IsShadow ν ((α : ENNReal) • Measure.dirac x) (quantileSlice ν s s') := by sorry

end MartOT.Shadow
