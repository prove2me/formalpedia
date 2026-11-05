-- Prove2me | Theorems.Thm_MartOT_Abs_optimizers_convex
-- name    : MartOT.Abs.optimizers_convex
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-11-05T04:54:55.531901+00:00
-- url     : https://prove2.me/theorems/31b73d29-f3b3-4de4-9792-1f2c2bad4dfd
-- title:
--   Proof of Theorem 7.4, p. 46 — for c = |y − x| the set of optimal martingale plans is convex
-- statement:
--   Let $\mu\preceq_C\nu$ be probability measures on $\mathbb R$ and $c(x,y)=|y-x|$. If $\pi$ and $\pi'$ are optimal martingale transport plans for $c$, then so is every convex combination $t\pi+(1-t)\pi'$, $t\in[0,1]$.
--
--   The proof of Theorem 7.4 (p. 46) applies Lemma 5.6 to the set of optimizers, which requires it to be a nonempty convex set of martingale plans: $\Pi_M(\mu,\nu)$ is convex and $\pi\mapsto\int c\,d\pi$ is affine, with finite values here since $|y-x|$ is $\pi$-integrable.
--
--   **Formalization Note** Optimality is `IsOptimal`: $\pi\in\Pi_M(\mu,\nu)$ and $\int c\,d\pi\le\int c\,d\pi'$ for all $\pi'\in\Pi_M(\mu,\nu)$, with costs in `EReal`. The combination is $\mathrm{ofReal}(t)\cdot\pi+\mathrm{ofReal}(1-t)\cdot\pi'$ as measures.
-- source:
--   arXiv:1208.1509v2 (Beiglböck–Juillet), proof of Theorem 7.4, p. 46 (the set of optimizers to which Lemma 5.6, p. 36, is applied is convex)

import Mathlib
import Definitions.Def_MartOT_Var_Setting

namespace MartOT.Abs

open MeasureTheory

theorem optimizers_convex (μ ν : Measure ℝ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (hμν : MartOT.Var.ConvexLE μ ν) (π π' : Measure (ℝ × ℝ))
    (hπ : MartOT.Var.IsOptimal (fun x y => |y - x|) μ ν π)
    (hπ' : MartOT.Var.IsOptimal (fun x y => |y - x|) μ ν π')
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    MartOT.Var.IsOptimal (fun x y => |y - x|) μ ν
      (ENNReal.ofReal t • π + ENNReal.ofReal (1 - t) • π') := by sorry

end MartOT.Abs
