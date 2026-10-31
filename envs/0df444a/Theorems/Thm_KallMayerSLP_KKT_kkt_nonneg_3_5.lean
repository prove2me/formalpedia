-- Prove2me | Theorems.Thm_KallMayerSLP_KKT_kkt_nonneg_3_5
-- name    : KallMayerSLP.KKT.kkt_nonneg_3_5
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:08:47.487994+00:00
-- url     : https://prove2.me/theorems/7cf5a2fa-5dbe-4c92-8c0b-d1f8e4d553c9
-- title:
--   KKT conditions (3.5) for a convex program with nonnegative variables
-- statement:
--   Throughout, $f:\mathbb R^n\to\mathbb R$ and $g_1,\dots,g_m:\mathbb R^n\to\mathbb R$ are convex and continuously differentiable, the book's standing assumptions for the program
--   $$
--   \min f(x)\quad\text{s.t.}\quad g_i(x)\le0,\ i=1,\dots,m,\tag{3.1}
--   $$
--   with feasible set $\mathcal B=\{x\mid g_i(x)\le 0,\ i=1,\dots,m\}$.
--
--   Consider the program
--   $$
--   \min\{f(x)\mid g(x)\le 0,\ x\ge 0\},\tag{3.4}
--   $$
--   and assume the Slater condition for its nonlinear constraints: some $\tilde x\ge 0$ has $g_i(\tilde x)<0$ for all $i$. Then $\hat x$ solves (3.4) if and only if there is $\hat u\in\mathbb R^m$ with
--
--   1. $\nabla f(\hat x)+\sum_{i=1}^m\hat u_i\nabla g_i(\hat x)\ge 0$ (componentwise),
--   2. $\hat x^{\mathsf T}\big(\nabla f(\hat x)+\sum_{i=1}^m\hat u_i\nabla g_i(\hat x)\big)=0$,
--   3. $g(\hat x)\le 0$,
--   4. $\hat u^{\mathsf T}g(\hat x)=0$,
--   5. $\hat x\ge 0$,
--   6. $\hat u\ge 0$. $\qquad$ (3.5)
--
--   This is the form of the KKT conditions for programs with sign constraints on the variables.
--
--   Differences from the source:
--   - encoding: ℝⁿ with zᵀv → EuclideanSpace ℝ (Fin n) with the inner product ⟪z, v⟫ and Mathlib's gradient; reason: Lean convention; the same space and the same gradient for differentiable functions
--   - reading: 'we get immediately the KKT conditions (3.5)', with no regularity condition written → x̂ solves (3.4) ↔ ∃ û with (3.5), assuming some x̃ ≥ 0 with gᵢ(x̃) < 0 for all i; reason: the text derives (3.5) from Proposition 3.4, whose Slater condition is, by p.63, needed for the nonlinear constraints only; of the two readings (x̃ > 0 or x̃ ≥ 0) this is the stronger theorem
-- source:
--   Kall & Mayer, Stochastic Linear Programming: Models, Theory, and Computation (Kluwer/Springer 2005), Chapter 1, §3.1, eqs. (3.4)–(3.5), p.65 (PDF 76)

import Mathlib

open scoped RealInnerProductSpace

namespace KallMayerSLP.KKT

/-- **KKT conditions (3.5) for the program (3.4) with nonnegative variables.**
Kall & Mayer, *Stochastic Linear Programming* (2005), Chapter 1, §3.1, eqs. (3.4)–(3.5), p.65 (PDF 76): "If we have for instance the NLP
`min{f(x) | g(x) ≤ 0, x ≥ 0}` (3.4) with the vector valued function
`g(x) = (g₁(x), ⋯, g_m(x))ᵀ` and all `gᵢ` and `f` being continuously differentiable and convex as
before, we get immediately the KKT conditions
  i)   `∇f(x̂) + Σ_{i=1}^m ûᵢ∇gᵢ(x̂) ≥ 0`,
  ii)  `x̂ᵀ(∇f(x̂) + Σ_{i=1}^m ûᵢ∇gᵢ(x̂)) = 0`,
  iii) `g(x̂) ≤ 0`,
  iv)  `ûᵀg(x̂) = 0`,
  v)   `x̂ ≥ 0`,
  vi)  `û ≥ 0`." (3.5)

Here `f` and every `gᵢ` are convex on `ℝⁿ` and continuously differentiable (`ContDiff ℝ 1`), the
book's standing assumptions for (3.1) (p.61 and p.62), and the Slater condition holds in the form allowed on p.63 (strict inequality
for the nonlinear constraints `gᵢ` only): some `x̃ ≥ 0` has `gᵢ(x̃) < 0` for all `i`. Then `x̂`
solves (3.4) if and only if some `û ∈ ℝᵐ` satisfies (3.5).

**Formalization Note.** As for Proposition 3.4, "we get the KKT conditions" is the
characterization "`x̂` solves (3.4) iff `∃ û` with (3.5)". `x ≥ 0` is `∀ j, 0 ≤ x j`; i) is
componentwise; ii) is the inner product with `x̂`; iv) is the sum `Σ ûᵢ gᵢ(x̂)`. -/
theorem kkt_nonneg_3_5 {n m : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (g : Fin m → EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ConvexOn ℝ Set.univ f) (hg : ∀ i, ConvexOn ℝ Set.univ (g i))
    (hf1 : ContDiff ℝ 1 f) (hg1 : ∀ i, ContDiff ℝ 1 (g i))
    (hS : ∃ x : EuclideanSpace ℝ (Fin n), (∀ j, 0 ≤ x j) ∧ ∀ i, g i x < 0)
    (xh : EuclideanSpace ℝ (Fin n)) :
    ((∀ j, 0 ≤ xh j) ∧ (∀ i, g i xh ≤ 0) ∧
        ∀ y : EuclideanSpace ℝ (Fin n), (∀ j, 0 ≤ y j) → (∀ i, g i y ≤ 0) → f xh ≤ f y) ↔
      ∃ uh : Fin m → ℝ,
        (∀ j, 0 ≤ (gradient f xh + ∑ i, uh i • gradient (g i) xh) j) ∧
        ⟪xh, gradient f xh + ∑ i, uh i • gradient (g i) xh⟫ = 0 ∧
        (∀ i, g i xh ≤ 0) ∧
        ∑ i, uh i * g i xh = 0 ∧
        (∀ j, 0 ≤ xh j) ∧
        0 ≤ uh := by sorry

end KallMayerSLP.KKT
