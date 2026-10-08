-- Prove2me | Theorems.Thm_MartOT_Curtain_theorem_4_18
-- name    : MartOT.Curtain.theorem_4_18
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:20:00.503399+00:00
-- url     : https://prove2.me/theorems/57f471c2-e9c6-47fc-a3fa-8402189f09a5
-- title:
--   Theorem 4.18, p. 31 — π_lc: the unique plan taking µ|]−∞,x] to S^ν(µ|]−∞,x]) for all x, and it lies in Π_M(µ, ν)
-- statement:
--   Let $\mu,\nu$ be probability measures on $\mathbb R$ with finite first moments and $\mu\preceq_C\nu$. Then there is a unique probability measure $\pi_{\mathrm{lc}}$ on $\mathbb R\times\mathbb R$ that transports $\mu|_{]-\infty,x]}$ to its shadow $S^\nu(\mu|_{]-\infty,x]})$ for every $x$, that is,
--
--   $$\operatorname{proj}^x_\#\big(\pi_{\mathrm{lc}}|_{]-\infty,x]\times\mathbb R}\big)=\mu|_{]-\infty,x]},\qquad \operatorname{proj}^y_\#\big(\pi_{\mathrm{lc}}|_{]-\infty,x]\times\mathbb R}\big)=S^\nu(\mu|_{]-\infty,x]})\qquad(x\in\mathbb R).$$
--
--   Moreover $\pi_{\mathrm{lc}}$ is a martingale transport plan from $\mu$ to $\nu$: $\pi_{\mathrm{lc}}\in\Pi_M(\mu,\nu)$.
--
--   This is the paper's formal definition of the **left-curtain coupling**: the shadows of the initial segments of $\mu$ are laid onto $\nu$ like a curtain closed from the left.
--
--   **Formalization Note** The defining property is the predicate `IsLeftCurtain μ ν π`, which requires $\pi$ finite and the two displayed identities for every $x$. The statement asserts (a) exactly one measure on $\mathbb R^2$ has this property, and (b) every such measure is a probability measure and lies in $\Pi_M(\mu,\nu)$. Uniqueness among finite measures is the page's uniqueness among probability measures, by (b).
-- source:
--   arXiv:1208.1509v2, Theorem 4.18, p. 31

import Mathlib
import Definitions.Def_MartOT_Var_Setting

namespace MartOT.Curtain

open MeasureTheory

theorem theorem_4_18 (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμν : MartOT.Var.ConvexLE μ ν) :
    (∃! π : Measure (ℝ × ℝ), MartOT.Var.IsLeftCurtain μ ν π) ∧
      ∀ π : Measure (ℝ × ℝ), MartOT.Var.IsLeftCurtain μ ν π →
        IsProbabilityMeasure π ∧ MartOT.Var.IsMartingalePlan μ ν π := by sorry

end MartOT.Curtain
