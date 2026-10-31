-- Prove2me | Theorems.Thm_KallMayerSLP_ProbConstr_theorem_2_2
-- name    : KallMayerSLP.ProbConstr.theorem_2_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:12:21.48099+00:00
-- url     : https://prove2.me/theorems/883722b1-84bf-442b-884c-85f821588dd4
-- title:
--   Theorem 2.2, p.97 — $\mathcal B(0)$ and $\mathcal B(1)$ are convex
-- statement:
--   Let $\xi$ be a random vector in $\mathbb R^r$ with an arbitrary distribution $\mathbb P_\xi$, and let $T(\xi)$, $h(\xi)$ be measurable random data. Then the feasible sets
--   $$
--   \mathcal B(0)=\{x\mid G(x)\ge 0\}\qquad\text{and}\qquad \mathcal B(1)=\{x\mid G(x)\ge 1\}
--   $$
--   of the joint probability constraint are convex.
--
--   Without assumptions on the distribution these are the only levels at which convexity of $\mathcal B(\alpha)$ is guaranteed; at $\alpha=1$ the constraint asks for a "fat solution" that satisfies the random system almost surely.
--
--   Differences from the source:
--   - generalization: T(ξ) = T + Σ_j T^j ξ_j and h(ξ) = h + Σ_j h^j ξ_j affine in ξ (Notations, p.ix) → T(ξ), h(ξ) any functions of ξ whose entries are Borel measurable; reason: affine maps are continuous, hence measurable, so the book's data are an instance
--   - encoding: the distribution ℙ_ξ of ξ on (ℝ^r, 𝓑^r) → a probability measure μ on Fin r → ℝ with its Borel σ-algebra; probabilities are (μ A).toReal; reason: the real value of a probability is exact, so every instance is the same
-- source:
--   Kall & Mayer, Stochastic Linear Programming: Models, Theory, and Computation (Kluwer/Springer 2005), Chapter 2, Chapter 2, §2.1, Theorem 2.2, p.97 (PDF 107)

import Mathlib
import Definitions.Def_KallMayerSLP_ProbConstr_feasibleSet

open MeasureTheory

namespace KallMayerSLP.ProbConstr

/-- **Theorem 2.2** (Kall). `B(α)` is convex for `α = 0` and `α = 1`.

Kall & Mayer 2005, Chapter 2, Theorem 2.2, p.97 (PDF 107).

**Formalization Note.** `μ` is any probability measure on `ℝ^r` (the book: "without any assumptions concerning
the probability distribution of ξ"). The data `T(ξ)`, `h(ξ)` are any Borel measurable functions
of `ξ` (entrywise); the book's affine data (Notations, p.ix) are continuous, hence measurable, so
the statement contains the book's. -/
theorem theorem_2_2 {r m n : ℕ} (μ : Measure (Fin r → ℝ)) [IsProbabilityMeasure μ]
    (T : (Fin r → ℝ) → Matrix (Fin m) (Fin n) ℝ) (h : (Fin r → ℝ) → Fin m → ℝ)
    (hT : ∀ i j, Measurable fun ξ => T ξ i j) (hh : ∀ i, Measurable fun ξ => h ξ i) :
    Convex ℝ (feasibleSet μ T h 0) ∧ Convex ℝ (feasibleSet μ T h 1) := by sorry

end KallMayerSLP.ProbConstr
