-- Prove2me | Theorems.Thm_MartOT_Shadow_proposition_4_4
-- name    : MartOT.Shadow.proposition_4_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:19:56.008075+00:00
-- url     : https://prove2.me/theorems/e06cefdd-f460-4c78-b0a3-293768ffdefa
-- title:
--   Proposition 4.4, p. 21 — if µ ⪯E ν there is θ ≤ ν with µ ⪯C θ
-- statement:
--   Let $\mu,\nu$ be finite Borel measures on $\mathbb R$ with finite first moment. Write $\mu\preceq_E\nu$ (the **extended convex order**) if $\int\varphi\,d\mu\le\int\varphi\,d\nu$ for every *nonnegative* convex $\varphi:\mathbb R\to\mathbb R$, and $\mu\preceq_C\theta$ for the convex order (all convex $\varphi$, which forces equal masses).
--
--   If $\mu\preceq_E\nu$, then there exists a measure $\theta$ with
--   $$\theta\le\nu\qquad\text{and}\qquad\mu\preceq_C\theta .$$
--
--   The converse holds trivially, so the extended convex order is exactly "convex order into a part of $\nu$". This guarantees that the family over which the shadow is the minimum is nonempty.
-- source:
--   arXiv:1208.1509v2, Proposition 4.4, p. 21

import Mathlib
import Definitions.Def_MartOT_Var_Setting

namespace MartOT.Shadow

open MeasureTheory

theorem proposition_4_4 (μ ν : Measure ℝ) (h : MartOT.Var.ExtConvexLE μ ν) :
    ∃ θ : Measure ℝ, θ ≤ ν ∧ MartOT.Var.ConvexLE μ θ := by sorry

end MartOT.Shadow
