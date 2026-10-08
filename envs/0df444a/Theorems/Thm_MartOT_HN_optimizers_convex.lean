-- Prove2me | Theorems.Thm_MartOT_HN_optimizers_convex
-- name    : MartOT.HN.optimizers_convex
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:19:57.755374+00:00
-- url     : https://prove2.me/theorems/22e5caa9-cf7b-44f8-b990-12862f7aaf83
-- title:
--   Proof of Theorem 7.3, p. 45 — for c = −|y − x| the optimal martingale plans form a convex set
-- statement:
--   Let $\mu,\nu$ be probability measures on $\mathbb R$ in convex order and $c(x,y)=-|y-x|$. If $\pi$ and $\pi'$ are optimal martingale transport plans for $c$, then so is
--
--   $$t\,\pi+(1-t)\,\pi'\qquad\text{for every }t\in[0,1].$$
--
--   This is the "linear structure of the optimization problem" that lets Lemma 5.6 conclude uniqueness in Theorem 7.3. Costs are finite here because $|c(x,y)|\le|x|+|y|$ and $\mu,\nu$ have finite first moments.
--
--   **Formalization Note** The mixture is $\mathrm{ofReal}(t)\,\pi+\mathrm{ofReal}(1-t)\,\pi'$ with non-negative extended-real weights.
-- source:
--   arXiv:1208.1509v2, proof of Theorem 7.3, p. 45 (last paragraph: "the set of solutions is convex")

import Mathlib
import Definitions.Def_MartOT_Var_Setting

namespace MartOT.HN

open MeasureTheory

theorem optimizers_convex (μ ν : Measure ℝ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (hμν : MartOT.Var.ConvexLE μ ν) (π π' : Measure (ℝ × ℝ))
    (hπ : MartOT.Var.IsOptimal (fun x y => -|y - x|) μ ν π) (hπ' : MartOT.Var.IsOptimal (fun x y => -|y - x|) μ ν π')
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    MartOT.Var.IsOptimal (fun x y => -|y - x|) μ ν (ENNReal.ofReal t • π + ENNReal.ofReal (1 - t) • π') := by sorry

end MartOT.HN
