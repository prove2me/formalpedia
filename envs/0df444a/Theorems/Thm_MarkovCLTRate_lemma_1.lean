-- Prove2me | Theorems.Thm_MarkovCLTRate_lemma_1
-- name    : MarkovCLTRate.lemma_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:26:11.30836+00:00
-- url     : https://prove2.me/theorems/07ba20aa-6a2a-4b8b-b3f2-55a7e10405d8
-- title:
--   Lemma 1: regularity of the Stein solution for Lipschitz test functions
-- statement:
--   Let $g\in Lip_L$ and let $f$ be the solution of Stein's equation
--   $$
--   g(u)-E(g(Z))=\Delta f(u)-u^T\nabla f(u),\qquad Z\sim N(0,I).\qquad(2)
--   $$
--   Then $f$ is twice continuously differentiable, solves (2) at every $u\in\Re^d$, and for every $\beta\in(0,1)$ and all $x,y,u_1,u_2\in\Re^d$:
--
--   1. $\|\nabla^2f(x)-\nabla^2f(y)\|_{op}\le\tilde C_1(d,\beta)\|x-y\|^\beta L$;
--   2. $|\Delta f(x)-\Delta f(y)|\le\tilde C_2(d,\beta)\|x-y\|^\beta L$;
--   3. $|\langle\nabla^2f(x),u_1u_2^T\rangle_{HS}|\le CL\|u_1\|\,\|u_2\|$,
--
--   where $\tilde C_1,\tilde C_2$ are the explicit constants of Lemma 1 and $C$ is a constant independent of $d$ and $\beta$. Here $\langle\cdot,\cdot\rangle_{HS}$ is the Hilbert–Schmidt (Frobenius) inner product.
--
--   The lemma, taken from Gallouët, Mijoule and Swan (2018) and Fang, Shao and Xu (2019), is the analytic input of the Stein-method bound of Theorem 1: items 1 and 3 control the two Taylor remainders and the matrix $A_{k,h}$.
--
--   **Formalization Note** $f$ is the Mehler solution. The pairing $\langle\nabla^2f(x),u_1u_2^T\rangle_{HS}=\sum_{ij}\partial_{ij}f(x)(u_1)_i(u_2)_j$ is the second derivative of $f$ at $x$ applied to $(u_1,u_2)$. The constant $C$ of item 3 is chosen before the dimension.
--
--   Differences from the source:
--   - reading: f the solution to Stein's equation → f = steinSolution g (Mehler form), asserted C² and to solve (2) everywhere; reason: Stein's equation determines f only up to an additive constant; the paper names the Mehler solution on p.11, and items 1-3 presuppose a twice differentiable f
--   - encoding: ⟨∇²f(x), u₁u₂ᵀ⟩_HS → fderiv ℝ (fderiv ℝ f) x u₁ u₂; reason: the Hilbert–Schmidt pairing with a rank-one matrix is the second derivative applied to (u₁, u₂); same number
--   - encoding: C a constant independent of d and β → ∃ C quantified before d, g, L, β, x, u₁, u₂; reason: the quantifier order expresses the independence
-- source:
--   Srikant, Rates of Convergence in the Central Limit Theorem for Markov Chains, with an Application to TD Learning, arXiv:2401.15719v5, Lemma 1, p.5

import Mathlib
import Definitions.Def_MarkovCLTRate_Basic
import Definitions.Def_MarkovCLTRate_Stein

open MeasureTheory ProbabilityTheory
open scoped ENNReal MatrixOrder RealInnerProductSpace

namespace MarkovCLTRate

/-- **Lemma 1** of arXiv:2401.15719v5, p.5 (from Gallouët–Mijoule–Swan 2018, Props. 2.2–2.3, and
Fang–Shao–Xu 2019, Thm. 3.1). Let `g ∈ Lip_L` and let `f` be the solution of Stein's equation
(2) `g(u) − E[g(Z)] = Δf(u) − uᵀ∇f(u)`, `Z ∼ N(0, I)`. Then `f` is twice continuously
differentiable, solves (2) everywhere, and for every `β ∈ (0, 1)` and all `x, y, u₁, u₂ ∈ ℜ^d`:
1. `‖∇²f(x) − ∇²f(y)‖_op ≤ C̃₁(d, β) ‖x − y‖^β L`;
2. `|Δf(x) − Δf(y)| ≤ C̃₂(d, β) ‖x − y‖^β L`;
3. `|⟨∇²f(x), u₁u₂ᵀ⟩_HS| ≤ C L ‖u₁‖ ‖u₂‖`, with a constant `C` independent of `d` and `β`.

**Formalization Note.** `f` is the Mehler solution `steinSolution g` (p.11); "the solution" of
Lemma 1 is read as this one, since solutions differ by constants. The Hilbert–Schmidt pairing
`⟨∇²f(x), u₁u₂ᵀ⟩_HS = Σ_{ij} ∂_{ij}f(x) (u₁)_i (u₂)_j` is the second derivative applied to
`(u₁, u₂)`. The constant `C` of item 3 is quantified before `d`. -/
theorem lemma_1 :
    ∃ C : ℝ, ∀ (d : ℕ) (g : Vec d → ℝ) (L : NNReal), LipschitzWith L g →
      ContDiff ℝ 2 (steinSolution g) ∧
      (∀ u, g u - ∫ z, g z ∂(stdGaussian (Vec d))
          = laplacian (steinSolution g) u - ⟪u, gradient (steinSolution g) u⟫) ∧
      (∀ β : ℝ, 0 < β → β < 1 → ∀ x y : Vec d,
          opNorm (hessMat (steinSolution g) x - hessMat (steinSolution g) y)
            ≤ C1t d β * ‖x - y‖ ^ β * L) ∧
      (∀ β : ℝ, 0 < β → β < 1 → ∀ x y : Vec d,
          |laplacian (steinSolution g) x - laplacian (steinSolution g) y|
            ≤ C2t d β * ‖x - y‖ ^ β * L) ∧
      (∀ x u₁ u₂ : Vec d,
          |fderiv ℝ (fderiv ℝ (steinSolution g)) x u₁ u₂| ≤ C * L * ‖u₁‖ * ‖u₂‖) := by sorry

end MarkovCLTRate
