-- Prove2me | Theorems.Thm_KallMayerSLP_ProbConstr_theorem_2_1
-- name    : KallMayerSLP.ProbConstr.theorem_2_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:12:09.210891+00:00
-- url     : https://prove2.me/theorems/602057bb-18c2-42f0-a853-5b3f91395ff9
-- title:
--   Theorem 2.1, p.97 — the feasible set $\mathcal B(\alpha)$ is closed
-- statement:
--   Let $\xi$ be a random vector in $\mathbb R^r$ with an arbitrary distribution $\mathbb P_\xi$, and let $T(\xi)$, $h(\xi)$ be measurable random data. Then for every level $\alpha\in\mathbb R$ the feasible set
--   $$
--   \mathcal B(\alpha)=\{x\in\mathbb R^n\mid \mathbb P_\xi(T(\xi)x\ge h(\xi))\ge\alpha\}
--   $$
--   is closed.
--
--   Closedness matters both for the existence of optimal solutions of chance-constrained programs and for their numerical solution; it holds without any assumption on the distribution of $\xi$.
--
--   Differences from the source:
--   - generalization: T(ξ) = T + Σ_j T^j ξ_j and h(ξ) = h + Σ_j h^j ξ_j affine in ξ (Notations, p.ix) → T(ξ), h(ξ) any functions of ξ whose entries are Borel measurable; reason: affine maps are continuous, hence measurable, so the book's data are an instance
--   - encoding: the distribution ℙ_ξ of ξ on (ℝ^r, 𝓑^r) → a probability measure μ on Fin r → ℝ with its Borel σ-algebra; probabilities are (μ A).toReal; reason: the real value of a probability is exact, so every instance is the same
-- source:
--   Kall & Mayer, Stochastic Linear Programming: Models, Theory, and Computation (Kluwer/Springer 2005), Chapter 2, Chapter 2, §2.1, Theorem 2.1, p.97 (PDF 107)

import Mathlib
import Definitions.Def_KallMayerSLP_ProbConstr_feasibleSet

open MeasureTheory

namespace KallMayerSLP.ProbConstr

/-- **Theorem 2.1.** The set `B(α)` is closed.

Kall & Mayer 2005, Chapter 2, Theorem 2.1, p.97 (PDF 107) (proof cited: Kall and Wallace,
Proposition 1.7).

**Formalization Note.** `μ` is any probability measure on `ℝ^r` (the book: "without any assumptions concerning
the probability distribution of ξ"). The data `T(ξ)`, `h(ξ)` are any Borel measurable functions
of `ξ` (entrywise); the book's affine data (Notations, p.ix) are continuous, hence measurable, so
the statement contains the book's. Every real level `α`; `ℝ^n` is `Fin n → ℝ` with its product
(Euclidean) topology. -/
theorem theorem_2_1 {r m n : ℕ} (μ : Measure (Fin r → ℝ)) [IsProbabilityMeasure μ]
    (T : (Fin r → ℝ) → Matrix (Fin m) (Fin n) ℝ) (h : (Fin r → ℝ) → Fin m → ℝ)
    (hT : ∀ i j, Measurable fun ξ => T ξ i j) (hh : ∀ i, Measurable fun ξ => h ξ i) (α : ℝ) :
    IsClosed (feasibleSet μ T h α) := by sorry

end KallMayerSLP.ProbConstr
