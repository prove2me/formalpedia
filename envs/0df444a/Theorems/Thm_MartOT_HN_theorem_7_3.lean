-- Prove2me | Theorems.Thm_MartOT_HN_theorem_7_3
-- name    : MartOT.HN.theorem_7_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:20:35.083126+00:00
-- url     : https://prove2.me/theorems/411112f1-16db-4566-9c6d-2562b3ab91d0
-- title:
--   Theorem 7.3, p. 43 — for c = −|y − x| and continuous µ the optimal martingale plan is unique and lives on two nondecreasing graphs T₁ ≤ id ≤ T₂
-- statement:
--   Let $\mu$ and $\nu$ be probability measures on $\mathbb R$ in convex order, and assume that $\mu$ is continuous: $\mu(\{x\})=0$ for every $x\in\mathbb R$. Consider the Hobson–Neuberger cost $c(x,y)=-|y-x|$.
--
--   1. There is a unique optimal martingale transport plan $\pi_{\mathrm{HN}}\in\Pi_M(\mu,\nu)$ for $c$, i.e. a unique minimizer of $\pi\mapsto\int c\,d\pi$ over $\Pi_M(\mu,\nu)$.
--   2. There are a Borel set $S\subseteq\mathbb R$ with $\mu(\mathbb R\setminus S)=0$ and two functions $T_1,T_2$, nondecreasing on $S$, such that
--
--   $$T_1(x)\le x\le T_2(x)\quad(x\in S),\qquad \pi_{\mathrm{HN}}\Big(\big\{(x,y):x\in S,\ y\in\{T_1(x),T_2(x)\}\big\}\Big)=1 .$$
--
--   Minimizing $-|y-x|$ maximizes the expected absolute displacement $\int|y-x|\,d\pi$; Hobson and Neuberger studied this problem for the robust pricing of forward-start straddles. The theorem identifies the optimizer as a plan that splits each starting point into at most two destinations, one below and one above, along two monotone maps.
--
--   **Formalization Note** The paper states $T_1,T_2:\mathbb R\to\mathbb R$ nondecreasing on all of $\mathbb R$ with $T_1(x)\le x\le T_2(x)$ for every $x$. Read literally this is false whenever $\mu$ has bounded support and $\nu$ does not (for instance $\mu$ uniform on $[0,1]$ and $\nu$ the law of $U+Z$ with $Z$ independent, centred and unbounded): monotone real maps are bounded on $[0,1]$, so a plan carried by their graphs over $[0,1]$ would have a boundedly supported second marginal. The paper's proof constructs $T_1,T_2$ on $\operatorname{proj}^x(\Gamma)$ with $T_1(x)\le x\le T_2(x)$ for $\mu$-almost every $x$. The statement is therefore made on a Borel set $S$ of full $\mu$-measure, as in the paper's Corollary 1.6. Continuity of $\mu$ is written $\mu(\{x\})=0$ for every $x$. Uniqueness is among all optimal plans in $\Pi_M(\mu,\nu)$.
-- source:
--   arXiv:1208.1509v2, Theorem 7.3, p. 43 (proof pp. 44–45)

import Mathlib
import Definitions.Def_MartOT_Var_Setting

namespace MartOT.HN

open MeasureTheory

theorem theorem_7_3 (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμν : MartOT.Var.ConvexLE μ ν) (hμc : ∀ x : ℝ, μ {x} = 0) :
    ∃ π : Measure (ℝ × ℝ), MartOT.Var.IsOptimal (fun x y => -|y - x|) μ ν π ∧
      (∀ π' : Measure (ℝ × ℝ), MartOT.Var.IsOptimal (fun x y => -|y - x|) μ ν π' → π' = π) ∧
      ∃ (S : Set ℝ) (T₁ T₂ : ℝ → ℝ), MeasurableSet S ∧ μ Sᶜ = 0 ∧
        MonotoneOn T₁ S ∧ MonotoneOn T₂ S ∧ (∀ x ∈ S, T₁ x ≤ x ∧ x ≤ T₂ x) ∧
        π {p : ℝ × ℝ | ¬ (p.1 ∈ S ∧ (p.2 = T₁ p.1 ∨ p.2 = T₂ p.1))} = 0 := by sorry

end MartOT.HN
