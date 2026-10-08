-- Prove2me | Theorems.Thm_MartOT_Card_theorem_7_1
-- name    : MartOT.Card.theorem_7_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:19:10.551727+00:00
-- url     : https://prove2.me/theorems/c6f3b425-6978-410a-9f46-5177a1506d53
-- title:
--   Theorem 7.1, p. 38 — for c = h(y − x) with affine lines meeting h′ in ≤ k points, an optimal plan's kernel has ≤ k support points at every non-atom
-- statement:
--   Let $\mu,\nu$ be probability measures on $\mathbb R$ in convex order, and let the cost be $c(x,y)=h(y-x)$ for a twice continuously differentiable $h:\mathbb R\to\mathbb R$. Assume that affine functions $x\mapsto sx+t$ meet $h'$ in at most $k$ points, i.e. $|\{x:h'(x)=sx+t\}|\le k$ for all $s,t$. Assume that $c$ satisfies the sufficient integrability condition and that $\pi\in\Pi_M(\mu,\nu)$ is an optimal martingale transport plan with finite cost $\int c\,d\pi<+\infty$. Then:
--
--   1. there is a disintegration $(\pi_x)_{x\in\mathbb R}$ of $\pi$ with respect to $\mu$ such that for **every** $x\in\mathbb R$
--   $$\mu(\{x\})>0\qquad\text{or}\qquad \operatorname{card}(\operatorname{spt}\pi_x)\le k;$$
--   2. if $\mu$ is continuous ($\mu(\{x\})=0$ for every $x$), then for **every** disintegration $(\pi_x)$ of $\pi$, $\operatorname{card}(\operatorname{spt}\pi_x)\le k$ for $\mu$-almost every $x$.
--
--   For example, $h(t)=t^4$ has $h'(t)=4t^3$, which meets every line in at most three points, so optimal plans for $c(x,y)=(y-x)^4$ split every non-atom of $\mu$ into at most three points. The theorem shows how the shape of the cost controls the sparsity of optimal martingale couplings.
--
--   **Formalization Note** "$\pi$ is an optimal transport plan" is read, as in Section 7 which derives its results from Lemma 1.11, as an optimal martingale plan between probability measures in convex order; the proof begins "Let $\pi$ be optimal and $\Gamma$ according to Lemma 1.11", so the hypotheses of that lemma are added: the sufficient integrability condition for $c$ and finite cost (Borel measurability of $c$ is automatic since $h$ is continuous). A disintegration is a Markov kernel $\kappa$ with $\pi=\mu\otimes\kappa$. For a probability measure on $\mathbb R$, $\operatorname{card}(\operatorname{spt}\pi_x)\le k$ is equivalent to $\pi_x$ being concentrated on a set of at most $k$ points, which is how it is written. Cardinalities are in $\mathbb N\cup\{\infty\}$, and $h'$ is Lean's `deriv h`.
-- source:
--   arXiv:1208.1509v2, Theorem 7.1, p. 38 (proof pp. 38–39)

import Mathlib
import Definitions.Def_MartOT_Var_Setting

namespace MartOT.Card

open MeasureTheory ProbabilityTheory

theorem theorem_7_1 (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμν : MartOT.Var.ConvexLE μ ν) (h : ℝ → ℝ) (hh : ContDiff ℝ 2 h) (k : ℕ)
    (hk : ∀ s t : ℝ, {x : ℝ | deriv h x = s * x + t}.encard ≤ k)
    (hint : MartOT.Var.SuffIntegrable μ ν (fun x y => h (y - x)))
    (π : Measure (ℝ × ℝ)) (hπ : MartOT.Var.IsOptimal (fun x y => h (y - x)) μ ν π)
    (hfin : MartOT.Var.cost (fun x y => h (y - x)) π < ⊤) :
    (∃ κ : Kernel ℝ ℝ, IsMarkovKernel κ ∧ π = μ ⊗ₘ κ ∧
      ∀ x : ℝ, 0 < μ {x} ∨ ∃ F : Set ℝ, F.encard ≤ k ∧ κ x Fᶜ = 0) ∧
    ((∀ x : ℝ, μ {x} = 0) → ∀ κ : Kernel ℝ ℝ, IsMarkovKernel κ → π = μ ⊗ₘ κ →
      ∀ᵐ x ∂μ, ∃ F : Set ℝ, F.encard ≤ k ∧ κ x Fᶜ = 0) := by sorry

end MartOT.Card
