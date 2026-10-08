-- Prove2me | Theorems.Thm_MartOT_Product_theorem_4_18
-- name    : MartOT.Product.theorem_4_18
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:19:49.036698+00:00
-- url     : https://prove2.me/theorems/03f4a957-ead4-42ba-9258-3ccc32905793
-- title:
--   Theorem 4.18, p. 31 — for finite µ ⪯C ν there is exactly one π_lc sending µ|]−∞,x] to S^ν(µ|]−∞,x]) for all x; π_lc ∈ Π_M(µ,ν)
-- statement:
--   Let $\mu,\nu$ be finite Borel measures on $\mathbb R$ with finite first moments and $\mu\preceq_C\nu$. For a measure $\pi$ on $\mathbb R\times\mathbb R$ and $x\in\mathbb R$ write $\pi|_{(-\infty,x]\times\mathbb R}$ for its restriction to the vertical half-plane, and $\mathrm{proj}^x_\#$, $\mathrm{proj}^y_\#$ for the two marginal maps.
--
--   **Theorem (definition of $\pi_{lc}$).** There is exactly one finite measure $\pi_{lc}$ on $\mathbb R\times\mathbb R$ such that for every $x\in\mathbb R$
--
--   $$\mathrm{proj}^x_\#\big(\pi_{lc}|_{(-\infty,x]\times\mathbb R}\big)=\mu|_{(-\infty,x]},\qquad \mathrm{proj}^y_\#\big(\pi_{lc}|_{(-\infty,x]\times\mathbb R}\big)=S^\nu\big(\mu|_{(-\infty,x]}\big).$$
--
--   Moreover $\pi_{lc}$ is a martingale transport plan from $\mu$ to $\nu$: $\pi_{lc}\in\Pi_M(\mu,\nu)$.
--
--   This is the formal definition of the **left-curtain coupling**: it transports each left part $\mu|_{(-\infty,x]}$ of $\mu$ onto its shadow in $\nu$.
--
--   **Formalization Note** The page states the theorem for probability measures $\mu,\nu$ and calls $\pi_{lc}$ a probability measure. Theorem 6.3, the goal of this mission, is about finite measures in convex order, so the statement here is for finite $\mu\preceq_C\nu$ and $\pi_{lc}$ is a finite measure (of mass $\mu(\mathbb R)$); the proof on the page does not use mass one. The defining property is the Setting layer's predicate `IsLeftCurtain μ ν π`, and the shadow is the predicate `IsShadow`.
-- source:
--   arXiv:1208.1509v2, Theorem 4.18, p. 31

import Mathlib
import Definitions.Def_MartOT_Var_Setting

namespace MartOT.Product

open MeasureTheory

/-- **Theorem 4.18** (Definition of `π_lc`, p. 31), for finite `μ ⪯C ν`: there is exactly one finite
measure `π` on `ℝ × ℝ` transporting `μ|]−∞,x]` to `S^ν(μ|]−∞,x])` for every `x`, and it is a martingale
transport plan from `μ` to `ν`. -/
theorem theorem_4_18 (μ ν : Measure ℝ) (hμν : MartOT.Var.ConvexLE μ ν) :
    (∃! π : Measure (ℝ × ℝ), MartOT.Var.IsLeftCurtain μ ν π) ∧
      ∀ π : Measure (ℝ × ℝ), MartOT.Var.IsLeftCurtain μ ν π → MartOT.Var.IsMartingalePlan μ ν π := by sorry

end MartOT.Product
