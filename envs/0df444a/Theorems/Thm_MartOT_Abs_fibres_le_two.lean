-- Prove2me | Theorems.Thm_MartOT_Abs_fibres_le_two
-- name    : MartOT.Abs.fibres_le_two
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:20:33.053074+00:00
-- url     : https://prove2.me/theorems/a6aa22d6-3e8a-4afa-b6a9-886411f6c1ac
-- title:
--   Proof of Theorem 7.4, p. 46 — an optimal plan for c = |y − x| lives on a Borel Γ with at most two off-diagonal points in each fibre
-- statement:
--   Let $\mu,\nu$ be probability measures on $\mathbb R$ in convex order, with $\mu$ continuous ($\mu(\{x\})=0$ for every $x$), and let $\pi$ be an optimal martingale transport plan for $c(x,y)=|y-x|$. Then there is a Borel set $\Gamma\subseteq\mathbb R^2$ with $\pi(\Gamma)=1$ such that
--
--   $$\big|\{y\in\mathbb R:\ (x,y)\in\Gamma,\ y\ne x\}\big|\le2\qquad\text{for every }x\in\mathbb R .$$
--
--   With $\bar\Gamma=\Gamma\setminus\Delta$ this is the paper's $|\bar\Gamma_x|\le2$ for every $x$. Together with the diagonal point it gives the bound $|\Gamma_x|\le3$ of Theorem 7.4, and it is why the moving part of an optimal plan lives on two graphs.
--
--   **Formalization Note** The page obtains this from the set $\Gamma$ of Lemma 1.11 "removing countably many points if necessary"; the statement asserts the resulting set. Continuity of $\mu$ is needed: if $\mu=\delta_0$ and $\nu$ is a three-point law with mean $0$, the only plan sends $0$ to three points. Cardinalities are in $\mathbb N\cup\{\infty\}$.
-- source:
--   arXiv:1208.1509v2, proof of Theorem 7.4, p. 46 (second paragraph)

import Mathlib
import Definitions.Def_MartOT_Var_Setting

namespace MartOT.Abs

open MeasureTheory

theorem fibres_le_two (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμν : MartOT.Var.ConvexLE μ ν) (hμc : ∀ x : ℝ, μ {x} = 0) (π : Measure (ℝ × ℝ))
    (hπ : MartOT.Var.IsOptimal (fun x y => |y - x|) μ ν π) :
    ∃ Γ : Set (ℝ × ℝ), MeasurableSet Γ ∧ π Γᶜ = 0 ∧
      ∀ x : ℝ, {y : ℝ | (x, y) ∈ Γ ∧ y ≠ x}.encard ≤ 2 := by sorry

end MartOT.Abs
