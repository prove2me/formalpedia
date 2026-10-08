-- Prove2me | Theorems.Thm_MartOT_Shadow_lemma_4_6
-- name    : MartOT.Shadow.lemma_4_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:19:42.62025+00:00
-- url     : https://prove2.me/theorems/4f9bd4e9-a903-4a71-9f10-b055976fe68e
-- title:
--   Lemma 4.6, p. 23 — shadow embedding: if µ ⪯E ν, the shadow S^ν(µ) exists, is unique, and satisfies (iii′)
-- statement:
--   Let $\mu,\nu$ be finite Borel measures on $\mathbb R$ with finite first moment, and assume $\mu\preceq_E\nu$ (extended convex order: $\int\varphi\,d\mu\le\int\varphi\,d\nu$ for every nonnegative convex $\varphi$). Call $\eta$ a **shadow of $\mu$ in $\nu$** if
--
--   1. $\eta\le\nu$;
--   2. $\mu\preceq_C\eta$ (convex order);
--   3. $\eta\preceq_C\eta'$ for every measure $\eta'$ with $\eta'\le\nu$ and $\mu\preceq_C\eta'$.
--
--   Then there exists exactly one shadow, denoted $S^\nu(\mu)$. Moreover it satisfies
--
--   (iii′) if $\eta'\le\nu$ and $\mu\preceq_E\eta'$, then
--   $$S^\nu(\mu)\preceq_E\eta' .$$
--
--   The shadow is the convex-order-least way of embedding $\mu$ into $\nu$ as a martingale target; it is the building block of the left-curtain coupling.
--
--   **Formalization Note** Shadows are encoded as the predicate `IsShadow ν μ η` (properties (i)–(iii) of Lemma 4.6), never as a chosen function; by Lemma 4.6 a shadow exists and is unique under the stated hypotheses, so quantifying over all $\eta$ with `IsShadow` is equivalent to speaking of $S^\nu(\mu)$. The subtraction $\nu-\eta$ is Mathlib's truncated subtraction of measures; it is the paper's difference whenever $\eta\le\nu$, which is guaranteed here by property (i) of the shadow. Uniqueness is part of the conclusion (`∃!`); antisymmetry of $\preceq_C$, on which it rests, is not assumed anywhere.
-- source:
--   arXiv:1208.1509v2, Lemma 4.6, p. 23

import Mathlib
import Definitions.Def_MartOT_Var_Setting

namespace MartOT.Shadow

open MeasureTheory

theorem lemma_4_6 (μ ν : Measure ℝ) (hμ : MartOT.Var.InM μ) (hν : MartOT.Var.InM ν) (h : MartOT.Var.ExtConvexLE μ ν) :
    (∃! η : Measure ℝ, MartOT.Var.IsShadow ν μ η) ∧
    ∀ η : Measure ℝ, MartOT.Var.IsShadow ν μ η →
      ∀ η' : Measure ℝ, η' ≤ ν → MartOT.Var.ExtConvexLE μ η' → MartOT.Var.ExtConvexLE η η' := by sorry

end MartOT.Shadow
