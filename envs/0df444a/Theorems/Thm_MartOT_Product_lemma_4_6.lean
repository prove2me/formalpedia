-- Prove2me | Theorems.Thm_MartOT_Product_lemma_4_6
-- name    : MartOT.Product.lemma_4_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:19:44.568008+00:00
-- url     : https://prove2.me/theorems/6b10fb18-75fa-4dc3-9873-13a0ff7d5f0a
-- title:
--   Lemma 4.6, p. 23 — the shadow S^ν(µ) of µ ⪯E ν exists, is unique, and is ⪯E-below every η ≤ ν with µ ⪯E η
-- statement:
--   Let $\mathcal M$ be the finite Borel measures on $\mathbb R$ with finite first moment, $\preceq_C$ the convex order and $\preceq_E$ the extended convex order (comparison of $\int\varphi$ for nonnegative convex $\varphi$ only). For $\mu,\nu\in\mathcal M$, a measure $\eta$ is a **shadow of $\mu$ in $\nu$** if
--
--   1. $\eta\le\nu$ (setwise),
--   2. $\mu\preceq_C\eta$,
--   3. $\eta\preceq_C\eta'$ for every measure $\eta'$ satisfying 1 and 2.
--
--   **Lemma (shadow embedding).** Let $\mu,\nu\in\mathcal M$ with $\mu\preceq_E\nu$. Then there is exactly one shadow $S^\nu(\mu)$ of $\mu$ in $\nu$, and moreover
--
--   $$\eta\le\nu\ \text{ and }\ \mu\preceq_E\eta\quad\Longrightarrow\quad S^\nu(\mu)\preceq_E\eta .$$
--
--   The shadow is the convex-order-least part of $\nu$ into which $\mu$ can be embedded by a martingale; it is the building block of the left-curtain coupling, whose defining property prescribes the shadow $S^\nu(\mu|_{(-\infty,x]})$ for every $x$.
--
--   **Formalization Note** The shadow is the predicate `IsShadow ν μ η` (properties (i)–(iii)) of the Setting layer, so existence and uniqueness are stated together as `∃!`. The page's "As a consequence of (iii), the measure is uniquely determined" is that uniqueness. The hypotheses $\mu,\nu\in\mathcal M$ are kept as on the page, although $\mu\preceq_E\nu$ already includes them.
-- source:
--   arXiv:1208.1509v2, Lemma 4.6, p. 23

import Mathlib
import Definitions.Def_MartOT_Var_Setting

namespace MartOT.Product

open MeasureTheory

/-- **Lemma 4.6** (Shadow embedding, p. 23). For `μ, ν ∈ 𝓜` with `μ ⪯E ν` the shadow `S^ν(μ)` exists
and is unique, and it satisfies (iii′). -/
theorem lemma_4_6 (μ ν : Measure ℝ) (hμ : MartOT.Var.InM μ) (hν : MartOT.Var.InM ν) (hμν : MartOT.Var.ExtConvexLE μ ν) :
    (∃! η : Measure ℝ, MartOT.Var.IsShadow ν μ η) ∧
      ∀ η, MartOT.Var.IsShadow ν μ η → ∀ η' : Measure ℝ, η' ≤ ν → MartOT.Var.ExtConvexLE μ η' → MartOT.Var.ExtConvexLE η η' := by sorry

end MartOT.Product
