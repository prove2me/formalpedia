-- Prove2me | Theorems.Thm_MartOT_Opt_theorem_1_7
-- name    : MartOT.Opt.theorem_1_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:20:35.664353+00:00
-- url     : https://prove2.me/theorems/5b43ae57-2027-4980-aa3e-3236c82bef95
-- title:
--   Theorem 1.7 (= Theorem 6.1), pp. 6, 36 — for c(x, y) = h(y − x) with h′ strictly convex, π_lc is the unique optimal martingale transport plan
-- statement:
--   Let $\mu,\nu$ be probability measures on $\mathbb R$ in convex order, $\mu\preceq_C\nu$. Let $h:\mathbb R\to\mathbb R$ be differentiable with strictly convex derivative $h'$, and consider the cost $c(x,y)=h(y-x)$. Assume that $c$ satisfies the sufficient integrability condition, $c(x,y)\ge a(x)+b(y)$ for all $x,y$ with $a\in L^1(\mu)$, $b\in L^1(\nu)$, and that
--
--   $$C_M(\mu,\nu)=\inf_{\pi\in\Pi_M(\mu,\nu)}\int h(y-x)\,d\pi(x,y)<\infty .$$
--
--   Then the left-curtain coupling $\pi_{lc}$ is the unique optimizer: $\pi_{lc}$ belongs to $\Pi_M(\mu,\nu)$ and minimizes $\int c\,d\pi$ over $\Pi_M(\mu,\nu)$, and every minimizer equals $\pi_{lc}$.
--
--   An example is $h(z)=e^{z}$, i.e. $c(x,y)=\exp(y-x)$, which is nonnegative and so satisfies the integrability condition with $a=b=0$. The theorem singles out one canonical martingale coupling as optimal for a whole family of costs at once.
--
--   **Formalization Note** The left-curtain coupling is not built as a function: the conclusion asserts a measure $\pi$ with the defining property of $\pi_{lc}$ (Theorem 4.18), that $\pi$ is optimal, and that every optimal plan equals $\pi$. Neither the existence of an optimizer nor its uniqueness is assumed. Theorem 6.1 states the finiteness hypothesis as "there exists a finite martingale transport plan", which is equivalent to $C_M(\mu,\nu)<\infty$ in the extended reals. "Strictly convex derivative" is strict convexity of `deriv h` on $\mathbb R$, with $h$ differentiable everywhere.
-- source:
--   arXiv:1208.1509v2, Theorem 1.7, p. 6; proved as Theorem 6.1, pp. 36–37

import Mathlib
import Definitions.Def_MartOT_Var_Setting

namespace MartOT.Opt

open MeasureTheory

theorem theorem_1_7 (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμν : MartOT.Var.ConvexLE μ ν) (h : ℝ → ℝ) (hd : Differentiable ℝ h)
    (hconv : StrictConvexOn ℝ Set.univ (deriv h))
    (hint : MartOT.Var.SuffIntegrable μ ν (fun x y => h (y - x)))
    (hfin : MartOT.Var.CM (fun x y => h (y - x)) μ ν < ⊤) :
    ∃ π : Measure (ℝ × ℝ), MartOT.Var.IsLeftCurtain μ ν π ∧ MartOT.Var.IsOptimal (fun x y => h (y - x)) μ ν π ∧
      ∀ π' : Measure (ℝ × ℝ), MartOT.Var.IsOptimal (fun x y => h (y - x)) μ ν π' → π' = π := by sorry

end MartOT.Opt
