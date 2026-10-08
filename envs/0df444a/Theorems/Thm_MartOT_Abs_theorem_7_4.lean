-- Prove2me | Theorems.Thm_MartOT_Abs_theorem_7_4
-- name    : MartOT.Abs.theorem_7_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:21:44.566982+00:00
-- url     : https://prove2.me/theorems/8d989808-d08f-403f-806a-c0010f494a2e
-- title:
--   Theorem 7.4, p. 43 — for c = |y − x| and continuous µ the optimal martingale plan is unique, keeps µ ∧ ν in place and moves the rest along two graphs
-- statement:
--   Let $\mu,\nu$ be probability measures on $\mathbb R$ in convex order, $\mu\preceq_C\nu$, and assume that $\mu$ is continuous: $\mu(\{x\})=0$ for every $x\in\mathbb R$. Consider the martingale transport problem for the cost
--
--   $$c(x,y)=|y-x| .$$
--
--   1. There exists a unique optimal martingale transport plan $\pi_{\mathrm{abs}}\in\Pi_M(\mu,\nu)$.
--   2. There is a set $\Gamma\subseteq\mathbb R^2$ with $\pi_{\mathrm{abs}}(\Gamma^c)=0$ and $|\Gamma_x|\le3$ for every $x\in\mathbb R$, where $\Gamma_x=\{y:(x,y)\in\Gamma\}$.
--   3. More precisely, $\pi_{\mathrm{abs}}=\pi_{\mathrm{stay}}+\pi_{\mathrm{go}}$, where $\pi_{\mathrm{stay}}=(\mathrm{Id}\otimes\mathrm{Id})_\#(\mu\wedge\nu)$ is the image of the largest measure below $\mu$ and $\nu$ under $x\mapsto(x,x)$ (so it lives on the diagonal), and $\pi_{\mathrm{go}}$ is a measure concentrated on $\operatorname{graph}(T_1)\cup\operatorname{graph}(T_2)$ for some functions $T_1,T_2:\mathbb R\to\mathbb R$.
--
--   This is the structure theorem for the cost $|y-x|$, the counterpart of the Hobson–Neuberger cost $-|y-x|$ (Theorem 7.3). It describes the optimizer studied by Hobson and Klimmek: mass common to $\mu$ and $\nu$ does not move, and the remaining mass from each point $x$ is split between at most two destinations.
--
--   **Formalization Note** Optimality is minimality of $\int c\,d\pi$ over $\Pi_M(\mu,\nu)$, with costs in the extended reals (they are finite here, since $|y-x|\le|x|+|y|$). $\mu\wedge\nu$ is the infimum in Mathlib's complete lattice of measures. "Concentrated on" is "the complement is null"; as on the page, $\Gamma$, $T_1$, $T_2$ carry no measurability requirement. Continuity of $\mu$ cannot be dropped (Remark 7.7).
-- source:
--   arXiv:1208.1509v2, Theorem 7.4, p. 43

import Mathlib
import Definitions.Def_MartOT_Var_Setting

namespace MartOT.Abs

open MeasureTheory

theorem theorem_7_4 (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμν : MartOT.Var.ConvexLE μ ν) (hμc : ∀ x : ℝ, μ {x} = 0) :
    ∃ π : Measure (ℝ × ℝ), MartOT.Var.IsOptimal (fun x y => |y - x|) μ ν π ∧
      (∀ π' : Measure (ℝ × ℝ), MartOT.Var.IsOptimal (fun x y => |y - x|) μ ν π' → π' = π) ∧
      (∃ Γ : Set (ℝ × ℝ), π Γᶜ = 0 ∧ ∀ x : ℝ, {y : ℝ | (x, y) ∈ Γ}.encard ≤ 3) ∧
      ∃ πgo : Measure (ℝ × ℝ), π = (μ ⊓ ν).map (fun x : ℝ => (x, x)) + πgo ∧
        ∃ T₁ T₂ : ℝ → ℝ, πgo {p : ℝ × ℝ | p.2 ≠ T₁ p.1 ∧ p.2 ≠ T₂ p.1} = 0 := by sorry

end MartOT.Abs
