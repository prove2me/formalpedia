-- Prove2me | Theorems.Thm_MartOT_Opt_theorem_1_9
-- name    : MartOT.Opt.theorem_1_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:20:15.030397+00:00
-- url     : https://prove2.me/theorems/77f90e00-e21e-4bcb-ae39-2f884740ac15
-- title:
--   Theorem 1.9, p. 8 — for c = h(y − x), h′ strictly convex: monotone ⇔ optimal ⇔ ν^π_t is ⪯C-least for every t
-- statement:
--   Let $\mu,\nu$ be probability measures on $\mathbb R$ in convex order. Let $h:\mathbb R\to\mathbb R$ be differentiable with strictly convex derivative $h'$, and assume that $c(x,y)=h(y-x)$ satisfies the sufficient integrability condition. Assume moreover $C_M(\mu,\nu)<+\infty$, and let $\pi\in\Pi_M(\mu,\nu)$. For $t\in\mathbb R$ write $\nu^\pi_t=\operatorname{proj}^y_\#(\pi|_{]-\infty,t]\times\mathbb R})$. The following statements are equivalent:
--
--   1. $\pi$ is monotone (Definition 1.4);
--   2. $\pi$ is optimal for $C_M(\mu,\nu)$;
--   3. for every $\pi'\in\Pi_M(\mu,\nu)$ and every $t\in\mathbb R$,
--   $$\nu^\pi_t\preceq_C\nu^{\pi'}_t .$$
--
--   The page reads the third statement as "$\pi$ is the left-curtain coupling $\pi_{lc}$"; the statement formalizes the property the page writes.
--
--   **Formalization Note** The three statements are given as a `List.TFAE`.
-- source:
--   arXiv:1208.1509v2, Theorem 1.9, p. 8

import Mathlib
import Definitions.Def_MartOT_Var_Setting

namespace MartOT.Opt

open MeasureTheory

theorem theorem_1_9 (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμν : MartOT.Var.ConvexLE μ ν) (h : ℝ → ℝ) (hd : Differentiable ℝ h)
    (hconv : StrictConvexOn ℝ Set.univ (deriv h))
    (hint : MartOT.Var.SuffIntegrable μ ν (fun x y => h (y - x)))
    (hfin : MartOT.Var.CM (fun x y => h (y - x)) μ ν < ⊤) (π : Measure (ℝ × ℝ))
    (hπ : MartOT.Var.IsMartingalePlan μ ν π) :
    List.TFAE
      [MartOT.Var.IsLeftMonotone π,
       MartOT.Var.IsOptimal (fun x y => h (y - x)) μ ν π,
       ∀ (π' : Measure (ℝ × ℝ)) (t : ℝ), MartOT.Var.IsMartingalePlan μ ν π' →
         MartOT.Var.ConvexLE (MartOT.Var.targetUpTo π t) (MartOT.Var.targetUpTo π' t)] := by sorry

end MartOT.Opt
