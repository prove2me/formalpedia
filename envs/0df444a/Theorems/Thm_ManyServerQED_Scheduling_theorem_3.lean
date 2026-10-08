-- Prove2me | Theorems.Thm_ManyServerQED_Scheduling_theorem_3
-- name    : ManyServerQED.Scheduling.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T11:04:27.216956+00:00
-- url     : https://prove2.me/theorems/fe3a1164-d344-4d86-a353-1ac3b38b1245
-- title:
--   Theorem 3 — the HJB equation has a unique $C^2_{\mathrm{pol}}$ solution, it equals $V$, and an optimal Markov policy exists
-- statement:
--   Let $k\ge1$, $(\ell,\mu,\theta,r)$ be diffusion data and $\gamma>0$. Assume $L$ is continuous and satisfies Assumption 2(i), (iii) and (iv), with Hölder exponent $\varrho\in(0,1)$. Then:
--   1. there is a classical solution $f\in C^{2,\varrho}_{\mathrm{pol}}(\mathbb R^k)$ of the HJB equation
--   $$
--   \tfrac12\sum_ir_i^2\,\partial^2_{x_i}f+H(x,Df)-\gamma f=0,\qquad H(x,p)=\inf_{u\in\mathbb S^k}[b(x,u)\cdot p+L(x,u)],\qquad(41)
--   $$
--   satisfying the growth condition (42);
--   2. this solution is unique in $C^2_{\mathrm{pol}}(\mathbb R^k)$;
--   3. $V=f$;
--   4. there is a measurable Markov control policy $h:\mathbb R^k\to\mathbb S^k$ that is optimal for every initial point $x$. That is, for each $x$ there are an admissible system $\pi$ and a controlled process $X$ for $x$ and $\pi$ with $u_s=h(X_s)$ for all $s\ge0$, $P$-a.s., and $V(x)=C(x,\pi)$.
--
--   Item 4 is Theorem 1 of the paper. The HJB solution and its minimizers are what the proposed scheduling policy is built from.
--
--   **Formalization Note** $V$ takes values in $[0,\infty]$, so "$V=f$" is stated as $f(x)\ge0$ and $V(x)=f(x)$ (via `ENNReal.ofReal`) for every $x$. The Hölder exponent $\varrho$ of the conclusion is the exponent of Assumption 2(iii).
-- source:
--   Atar, Mandelbaum & Reiman, Scheduling a Multi Class Queue with Many Exponential Servers: Asymptotic Optimality in Heavy Traffic, arXiv:math/0407058v1 (reprint of Ann. Appl. Probab. 14(3), 2004), p. 27, Theorem 3 (with Theorem 1, p. 18)

import Mathlib
import Definitions.Def_ManyServerQED_Scheduling_Diffusion

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace ManyServerQED.Scheduling

/-- Theorem 3 (p. 27), with Theorem 1 (p. 18) as its last clause: if `L` is continuous and satisfies
Assumption 2(i), (iii), (iv), then the HJB equation (41) has a classical solution
`f ∈ C^{2,ϱ}_pol(ℝ^k)`, unique in `C²_pol(ℝ^k)`, the value function equals `f`, and there is a
measurable `h : ℝ^k → 𝕊^k` that is a Markov control policy optimal for every initial point. -/
theorem theorem_3 {k : ℕ} [NeZero k] (D : DiffusionData k) (L : (Fin k → ℝ) → (Fin k → ℝ) → ℝ)
    (ϱ mL γ : ℝ) (hγ : 0 < γ) (hL : CostAssumptions L ϱ mL) :
    ∃ f : (Fin k → ℝ) → ℝ, IsC2RhoPol ϱ f ∧ IsHJBSolution D L γ f ∧
      (∀ g : (Fin k → ℝ) → ℝ, IsC2Pol g → IsHJBSolution D L γ g → g = f) ∧
      (∀ x, 0 ≤ f x ∧ value D L γ x = ENNReal.ofReal (f x)) ∧
      ∃ h : (Fin k → ℝ) → (Fin k → ℝ), Measurable h ∧ (∀ x, h x ∈ stdSimplex ℝ (Fin k)) ∧
        ∀ x, ∃ (π : AdmissibleSystem k) (X : ℝ≥0 → π.Ω → Fin k → ℝ),
          IsControlledProcess D π x X ∧ (∀ᵐ ω ∂π.P, ∀ s, π.u s ω = h (X s ω)) ∧
            value D L γ x = diffCost L γ π X := by sorry

end ManyServerQED.Scheduling
