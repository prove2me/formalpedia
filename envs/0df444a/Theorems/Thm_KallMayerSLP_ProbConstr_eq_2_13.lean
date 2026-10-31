-- Prove2me | Theorems.Thm_KallMayerSLP_ProbConstr_eq_2_13
-- name    : KallMayerSLP.ProbConstr.eq_2_13
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:12:06.697002+00:00
-- url     : https://prove2.me/theorems/8f733f17-f0f4-4f0b-8059-522c1b2a0c3b
-- title:
--   (2.13), p.96 — $\mathcal B(\alpha)$ as a union of intersections of realized constraint sets
-- statement:
--   Let $\xi$ be a random vector in $\mathbb R^r$ with an arbitrary distribution $\mathbb P_\xi$, and let $T(\xi)$, $h(\xi)$ be measurable random data. For every level $\alpha\in\mathbb R$, the feasible set $\mathcal B(\alpha)=\{x\mid G(x)\ge\alpha\}$ satisfies $\mathcal B(\alpha)=\{x\mid S(x)\in\mathcal G_\alpha\}$ and
--   $$
--   \mathcal B(\alpha)=\bigcup_{A\in\mathcal G_\alpha}\{x\mid S(x)=A\}
--   =\bigcup_{A\in\mathcal G_\alpha}\{x\mid \forall\xi\in A:\ T(\xi)x\ge h(\xi)\}
--   =\bigcup_{A\in\mathcal G_\alpha}\ \bigcap_{\xi\in A}\{x\mid T(\xi)x\ge h(\xi)\},
--   $$
--   where $S(x)=\{\xi\mid T(\xi)x\ge h(\xi)\}$ and $\mathcal G_\alpha$ is the family of Borel events of probability at least $\alpha$.
--
--   This representation exhibits $\mathcal B(\alpha)$ as a union of convex sets; it specializes to (2.17) for a finite discrete distribution.
--
--   Differences from the source:
--   - generalization: T(ξ) = T + Σ_j T^j ξ_j and h(ξ) = h + Σ_j h^j ξ_j affine in ξ (Notations, p.ix) → T(ξ), h(ξ) any functions of ξ whose entries are Borel measurable; reason: affine maps are continuous, hence measurable, so the book's data are an instance
--   - encoding: the distribution ℙ_ξ of ξ on (ℝ^r, 𝓑^r) → a probability measure μ on Fin r → ℝ with its Borel σ-algebra; probabilities are (μ A).toReal; reason: the real value of a probability is exact, so every instance is the same
-- source:
--   Kall & Mayer, Stochastic Linear Programming: Models, Theory, and Computation (Kluwer/Springer 2005), Chapter 2, Chapter 2, §2.1, (2.13), p.96 (PDF 106)

import Mathlib
import Definitions.Def_KallMayerSLP_ProbConstr_feasibleEvent
import Definitions.Def_KallMayerSLP_ProbConstr_realizationSet
import Definitions.Def_KallMayerSLP_ProbConstr_levelEvents
import Definitions.Def_KallMayerSLP_ProbConstr_feasibleSet

open Matrix MeasureTheory

namespace KallMayerSLP.ProbConstr

/-- The representations of the feasible set of a joint probability constraint:
`B(α) = {x | S(x) ∈ 𝒢_α}` and (2.13)
`B(α) = ⋃_{A∈𝒢_α} {x | S(x) = A} = ⋃_{A∈𝒢_α} {x | ∀ξ ∈ A : T(ξ)x ≥ h(ξ)}
      = ⋃_{A∈𝒢_α} ⋂_{ξ∈A} {x | T(ξ)x ≥ h(ξ)}`.

Kall & Mayer 2005, Chapter 2, §2.1, (2.13), p.96 (PDF 106).

**Formalization Note.** `μ` is any probability measure on `ℝ^r` (the book: "without any assumptions concerning
the probability distribution of ξ"). The data `T(ξ)`, `h(ξ)` are any Borel measurable functions
of `ξ` (entrywise); the book's affine data (Notations, p.ix) are continuous, hence measurable, so
the statement contains the book's. Every real `α`. -/
theorem eq_2_13 {r m n : ℕ} (μ : Measure (Fin r → ℝ)) [IsProbabilityMeasure μ]
    (T : (Fin r → ℝ) → Matrix (Fin m) (Fin n) ℝ) (h : (Fin r → ℝ) → Fin m → ℝ)
    (hT : ∀ i j, Measurable fun ξ => T ξ i j) (hh : ∀ i, Measurable fun ξ => h ξ i) (α : ℝ) :
    feasibleSet μ T h α = {x | feasibleEvent T h x ∈ levelEvents μ α} ∧
    feasibleSet μ T h α = ⋃ A ∈ levelEvents μ α, {x | feasibleEvent T h x = A} ∧
    feasibleSet μ T h α = ⋃ A ∈ levelEvents μ α, {x | ∀ ξ ∈ A, h ξ ≤ T ξ *ᵥ x} ∧
    feasibleSet μ T h α = ⋃ A ∈ levelEvents μ α, ⋂ ξ ∈ A, realizationSet T h ξ := by sorry

end KallMayerSLP.ProbConstr
