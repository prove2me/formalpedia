-- Prove2me | Theorems.Thm_MartOT_Shadow_lemma_4_12
-- name    : MartOT.Shadow.lemma_4_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:20:12.260029+00:00
-- url     : https://prove2.me/theorems/415f827f-9385-4904-aa22-d7af0e2dcaa2
-- title:
--   Lemma 4.12, p. 27 — shadow of one atom and one measure: S^ν(δ + γ) = S^ν(δ) + S^{ν−S^ν(δ)}(γ)
-- statement:
--   Let $\delta=\alpha\,\delta_x$ be an atom of mass $\alpha\ge0$ at a point $x\in\mathbb R$, and let $\gamma,\nu$ be finite Borel measures on $\mathbb R$ with finite first moment. Assume $\delta+\gamma\preceq_E\nu$ (extended convex order). Then
--   $$\gamma\preceq_E\nu-S^\nu(\delta)$$
--   and
--   $$S^\nu(\delta+\gamma)=S^\nu(\delta)+S^{\nu-S^\nu(\delta)}(\gamma).$$
--
--   This is the associativity of shadows (Theorem 4.8) in the special case where the first measure is a single atom; iterating it gives the finitely-atomic case.
--
--   **Formalization Note** The conclusion is stated for every shadow $\eta_1$ of $\delta$ in $\nu$: $\gamma\preceq_E\nu-\eta_1$, and for every shadow $\eta_2$ of $\gamma$ in $\nu-\eta_1$, $\eta_1+\eta_2$ is a shadow of $\delta+\gamma$ in $\nu$. With existence and uniqueness of shadows (Lemma 4.6) this is the identity (10). Shadows are encoded as the predicate `IsShadow ν μ η` (properties (i)–(iii) of Lemma 4.6), never as a chosen function; by Lemma 4.6 a shadow exists and is unique under the stated hypotheses, so quantifying over all $\eta$ with `IsShadow` is equivalent to speaking of $S^\nu(\mu)$. The subtraction $\nu-\eta$ is Mathlib's truncated subtraction of measures; it is the paper's difference whenever $\eta\le\nu$, which is guaranteed here by property (i) of the shadow.
-- source:
--   arXiv:1208.1509v2, Lemma 4.12, eq. (10), p. 27

import Mathlib
import Definitions.Def_MartOT_Var_Setting

namespace MartOT.Shadow

open MeasureTheory NNReal

theorem lemma_4_12 (α : ℝ≥0) (x : ℝ) (γ ν : Measure ℝ) (hγ : MartOT.Var.InM γ) (hν : MartOT.Var.InM ν)
    (h : MartOT.Var.ExtConvexLE ((α : ENNReal) • Measure.dirac x + γ) ν) :
    ∀ η1 : Measure ℝ, MartOT.Var.IsShadow ν ((α : ENNReal) • Measure.dirac x) η1 →
      MartOT.Var.ExtConvexLE γ (ν - η1) ∧
      ∀ η2 : Measure ℝ, MartOT.Var.IsShadow (ν - η1) γ η2 →
        MartOT.Var.IsShadow ν ((α : ENNReal) • Measure.dirac x + γ) (η1 + η2) := by sorry

end MartOT.Shadow
