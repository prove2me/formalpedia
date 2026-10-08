-- Prove2me | Theorems.Thm_MartOT_Shadow_lemma_4_16
-- name    : MartOT.Shadow.lemma_4_16
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:20:51.447514+00:00
-- url     : https://prove2.me/theorems/78e6d073-27a9-490e-807e-4453708ca68f
-- title:
--   Lemma 4.16, p. 29 — shadow of one measure and one atom: δ ⪯E S^ν(γ + δ) − S^ν(γ) and S^ν(γ + δ) = S^ν(γ) + S^{ν−S^ν(γ)}(δ)
-- statement:
--   Let $\delta=\alpha\,\delta_x$ be an atom of mass $\alpha\ge0$ at a point $x\in\mathbb R$, and let $\gamma,\nu$ be finite Borel measures on $\mathbb R$ with finite first moment. Assume $\gamma+\delta\preceq_E\nu$ (extended convex order). Then $S^\nu(\gamma)\le S^\nu(\gamma+\delta)$,
--   $$\delta\preceq_E S^\nu(\gamma+\delta)-S^\nu(\gamma),$$
--   and
--   $$S^\nu(\gamma+\delta)=S^\nu(\gamma)+S^{\nu-S^\nu(\gamma)}(\delta).$$
--
--   Together with Lemma 4.12 this allows atoms to be added on either side of a sum, which is how Theorem 4.8 is reached for finitely atomic second summands.
--
--   **Formalization Note** The conclusion is stated for every shadow $\eta_1$ of $\gamma$ in $\nu$ and every shadow $\eta$ of $\gamma+\delta$ in $\nu$: $\eta_1\le\eta$, $\delta\preceq_E\eta-\eta_1$, and $\eta=\eta_1+\eta_2$ for every shadow $\eta_2$ of $\delta$ in $\nu-\eta_1$. The inequality $\eta_1\le\eta$ makes explicit that the page's difference $S^\nu(\gamma+\delta)-S^\nu(\gamma)$ is a measure; it also follows from (12). Shadows are encoded as the predicate `IsShadow ν μ η` (properties (i)–(iii) of Lemma 4.6), never as a chosen function; by Lemma 4.6 a shadow exists and is unique under the stated hypotheses, so quantifying over all $\eta$ with `IsShadow` is equivalent to speaking of $S^\nu(\mu)$. The subtraction $\nu-\eta$ is Mathlib's truncated subtraction of measures; it is the paper's difference whenever $\eta\le\nu$, which is guaranteed here by property (i) of the shadow.
-- source:
--   arXiv:1208.1509v2, Lemma 4.16, eq. (12), p. 29

import Mathlib
import Definitions.Def_MartOT_Var_Setting

namespace MartOT.Shadow

open MeasureTheory NNReal

theorem lemma_4_16 (α : ℝ≥0) (x : ℝ) (γ ν : Measure ℝ) (hγ : MartOT.Var.InM γ) (hν : MartOT.Var.InM ν)
    (h : MartOT.Var.ExtConvexLE (γ + (α : ENNReal) • Measure.dirac x) ν) :
    ∀ η1 : Measure ℝ, MartOT.Var.IsShadow ν γ η1 →
      ∀ η : Measure ℝ, MartOT.Var.IsShadow ν (γ + (α : ENNReal) • Measure.dirac x) η →
        η1 ≤ η ∧ MartOT.Var.ExtConvexLE ((α : ENNReal) • Measure.dirac x) (η - η1) ∧
        ∀ η2 : Measure ℝ, MartOT.Var.IsShadow (ν - η1) ((α : ENNReal) • Measure.dirac x) η2 →
          η = η1 + η2 := by sorry

end MartOT.Shadow
