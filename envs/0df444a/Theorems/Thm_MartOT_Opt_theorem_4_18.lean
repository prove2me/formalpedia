-- Prove2me | Theorems.Thm_MartOT_Opt_theorem_4_18
-- name    : MartOT.Opt.theorem_4_18
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:19:44.219957+00:00
-- url     : https://prove2.me/theorems/676fef3c-8140-4234-8cc6-e9a3c4bd2c81
-- title:
--   Theorem 4.18, p. 31 — for µ ⪯C ν there is a unique π_lc transporting µ|]−∞,x] to its shadow for every x, and π_lc ∈ Π_M(µ, ν)
-- statement:
--   Let $\mu,\nu$ be probability measures on $\mathbb R$ with $\mu\preceq_C\nu$. For a finite measure $\eta$ write $S^\nu(\eta)$ for its shadow in $\nu$ (Lemma 4.6). Then:
--
--   1. there is exactly one measure $\pi_{lc}$ on $\mathbb R\times\mathbb R$ such that, for every $x\in\mathbb R$,
--   $$\operatorname{proj}^x_\#\big(\pi_{lc}|_{]-\infty,x]\times\mathbb R}\big)=\mu|_{]-\infty,x]},\qquad \operatorname{proj}^y_\#\big(\pi_{lc}|_{]-\infty,x]\times\mathbb R}\big)=S^\nu\big(\mu|_{]-\infty,x]}\big);$$
--   2. this measure is a martingale transport plan from $\mu$ to $\nu$: $\pi_{lc}\in\Pi_M(\mu,\nu)$.
--
--   $\pi_{lc}$ is the **left-curtain coupling**; the goal of the mission identifies it as the unique optimizer.
--
--   **Formalization Note** The defining property is the predicate `IsLeftCurtain`, which asks $\pi$ to be a finite measure; the page asks for a probability measure, and the first condition forces total mass $\mu(\mathbb R)=1$, so the two readings agree. "Is the shadow" is the predicate of Lemma 4.6 (properties (i)–(iii)), not a function.
-- source:
--   arXiv:1208.1509v2, Theorem 4.18, p. 31

import Mathlib
import Definitions.Def_MartOT_Var_Setting

namespace MartOT.Opt

open MeasureTheory

theorem theorem_4_18 (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμν : MartOT.Var.ConvexLE μ ν) :
    (∃! π : Measure (ℝ × ℝ), MartOT.Var.IsLeftCurtain μ ν π) ∧
      ∀ π : Measure (ℝ × ℝ), MartOT.Var.IsLeftCurtain μ ν π → MartOT.Var.IsMartingalePlan μ ν π := by sorry

end MartOT.Opt
