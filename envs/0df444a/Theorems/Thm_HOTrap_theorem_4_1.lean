-- Prove2me | Theorems.Thm_HOTrap_theorem_4_1
-- name    : HOTrap.theorem_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T00:49:13.503336+00:00
-- url     : https://prove2.me/theorems/dc4a75e9-4480-458d-a8ca-4d8daec706a0
-- title:
--   Theorem 4.1 — higher-order gradient-only trapping
-- statement:
--   Let $d\ge2$, $p\ge1$, $\beta\in(0,1]$, $L\ge0$, $\Delta>0$ and $\nu=p+\beta$. For $f\in C^{p,\beta}(L)$ and $\varepsilon\in(0,1)$:
--
--   1. **Unconstrained optimization.** Given $x^0$ and a known bound $f(x^0)-\inf f\le\Delta$, an $\varepsilon$-stationary point can be found deterministically using $\tilde O\big(\varepsilon^{-\max\{d-1,\,\nu/(\nu-1)\}}\big)$ gradient queries, or with randomization using $\tilde O\big(\varepsilon^{-\max\{d-1,\,2\nu/(2\nu-1)\}}\big)$ gradient queries.
--   2. **Cube-constrained optimization.** A point $z\in[0,1]^d$ with $\|G_\gamma(z)\|_2\le\varepsilon$ for every $\gamma>0$ can be found deterministically using $\tilde O\big(\varepsilon^{-\max\{(d-1)/\nu,\,1/(\nu-1)\}}\big)$ gradient queries, or with randomization using $\tilde O\big(\varepsilon^{-\max\{(d-1)/\nu,\,2/(2\nu-1)\}}\big)$ gradient queries.
--
--   For any $\rho\in(0,1)$, the randomized algorithms succeed with probability at least $1-\rho$ and their query bounds hold for every seed, with only logarithmic dependence on $1/\rho$. All implementations use $O(\log(1/\varepsilon))$ adaptive rounds.
--
--   The constants depend only on $d,p,\beta,L,\Delta$. For $d=2$ and $\nu=2$ the unconstrained bound improves from $\tilde O(\varepsilon^{-2})$ to $\tilde O(\varepsilon^{-4/3})$ with randomization.
--
--   **Formalization Note** Each algorithm is chosen before $f$ and sees $f$ only through exact gradients at its own queries.
--
--   Differences from the source:
--   - reading: Õ(ε^{−a}) with d, p, β, L, Δ fixed → C ε^{−a} (1 + log(1/ε))^k, times (1 + log(1/ρ))^k in randomized mode, with C and k depending only on d, p, β, L, Δ and chosen before ε, ρ and x⁰; reason: the standard meaning; Proposition C.6 gives factors of this form, including the critical deterministic case
--   - reading: O(log(1/ε)) adaptive rounds → at most C (1 + log(1/ε)) rounds; reason: the form printed in the proof on p.85; a bare C log(1/ε) tends to 0 as ε → 1, where the algorithm still needs a round
--   - encoding: an algorithm with query count N(f, u) and a bound Q on the sup over f and u → a BatchAlg with fixed rounds and batch sizes, whose numQueries is bounded; reason: the round schedule of Algorithm 2 is deterministic and shorter runs pad with dummy queries up to the worst-case count, so the same algorithms qualify
--   - encoding: P_U(the returned point is an ε-solution) ≥ 1 − ρ, with an internal seed U → a seed space (Ω, P) chosen by the algorithm, before f, and a measurable seed set of probability at least 1 − ρ on which the output succeeds; reason: inner probability, which needs no measurability of the success event and implies the printed bound when that event is measurable
--   - encoding: f(x⁰) − inf f ≤ Δ < ∞, with Assumption 2.2 and the normalization f ≥ 0 → ∀ y, f x⁰ − f y ≤ Δ, with Δ > 0 and no sign condition on f; reason: equivalent to the gap bound, which implies f⋆ > −∞; adding a constant changes no gradient, so the normalization of p.13 excludes nothing
--   - reading: cube-constrained clause of Theorem 4.1, which names no lower bound → no lower bound on f and no Δ in the cube clauses; reason: the printed clause has neither; the proof of this case uses r₀ = 1 and Γ₀ = ∅ only (pp.73, 85)
-- source:
--   Zhou–Sugiyama–Suzuki, Finding Stationary Points under Higher-Order Smoothness: Trapping Algorithms and First-Order Lower Bounds, arXiv:2610.02791, Theorem 4.1, p.22; rounds and logarithmic factors from Proposition C.6, p.83, and the proof on p.85

import Mathlib
import Definitions.Def_HOTrap_HolderClass
import Definitions.Def_GeomDRSub_cube
import Definitions.Def_HOTrap_projGrad
import Definitions.Def_HOTrap_BatchAlg
import Definitions.Def_HOTrap_BatchAlg_run
import Definitions.Def_HOTrap_BatchAlg_numQueries

namespace HOTrap

/-- **Theorem 4.1 (higher-order gradient-only trapping).** Zhou–Sugiyama–Suzuki, *Finding Stationary Points under Higher-Order Smoothness: Trapping Algorithms and First-Order Lower Bounds*, arXiv:2610.02791, Theorem 4.1, p.22. With `d ≥ 2`, `p ≥ 1`,
`β ∈ (0,1]`, `ν := p + β`, for `f ∈ C^{p,β}(L)` and `ε ∈ (0,1)`: an `ε`-stationary point of `f` on `ℝ^d`, given
`x⁰` and `f(x⁰) − inf f ≤ Δ`, can be found with `Õ(ε^{−max{d−1, ν/(ν−1)}})` gradient queries deterministically and
`Õ(ε^{−max{d−1, 2ν/(2ν−1)}})` with randomization; a point `z ∈ [0,1]^d` with `∥G_γ(z)∥₂ ≤ ε` for every `γ > 0` can be
found with `Õ(ε^{−max{(d−1)/ν, 1/(ν−1)}})` queries deterministically and `Õ(ε^{−max{(d−1)/ν, 2/(2ν−1)}})` with
randomization. For any `ρ ∈ (0,1)` the randomized algorithms succeed with probability at least `1 − ρ`, their query
bounds hold for every seed with only logarithmic dependence on `1/ρ`, and all four use `O(log(1/ε))` adaptive rounds.

**Formalization Note** The constants `C`, `k` depend only on `d, p, β, L, Δ` and come before `ε`, `ρ`, `x⁰`. The
algorithm comes before `f` and receives `f` only through `gradient f`. `Õ(ε^{−a})` is `C ε^{−a} (1 + log(1/ε))^k`,
times `(1 + log(1/ρ))^k` in randomized mode, and `O(log(1/ε))` rounds is `C(1 + log(1/ε))`, the form of the proof
on p.85. The query count of a `BatchAlg` depends on neither `f` nor the seed. Success in randomized mode holds on a
measurable seed set of probability at least `1 − ρ`, so no probability of a possibly non-measurable event is taken.
The seed space is chosen by the algorithm. The gap bound is `∀ y, f x⁰ − f y ≤ Δ`. The cube clauses assume no
lower bound on `f`. -/
theorem theorem_4_1 (d p : ℕ) (hd : 2 ≤ d) (hp : 1 ≤ p) (β L Δ ν : ℝ) (hβ0 : 0 < β) (hβ1 : β ≤ 1)
    (hL : 0 ≤ L) (hΔ : 0 < Δ) (hν : ν = (p : ℝ) + β) :
    ∃ (C : ℝ) (k : ℕ), 0 < C ∧ ∀ ε : ℝ, 0 < ε → ε < 1 →
      (∀ x₀ : EuclideanSpace ℝ (Fin d), ∃ A : BatchAlg d Unit,
        (A.numQueries : ℝ) ≤
          C * ε ^ (-(max ((d : ℝ) - 1) (ν / (ν - 1)))) * (1 + Real.log (1 / ε)) ^ k ∧
        (A.rounds : ℝ) ≤ C * (1 + Real.log (1 / ε)) ∧
        ∀ f : EuclideanSpace ℝ (Fin d) → ℝ, HolderClass p β L f → (∀ y, f x₀ - f y ≤ Δ) →
          ‖gradient f (A.run (gradient f) ())‖ ≤ ε) ∧
      (∀ (x₀ : EuclideanSpace ℝ (Fin d)) (ρ : ℝ), 0 < ρ → ρ < 1 →
        ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : MeasureTheory.Measure Ω)
          (_ : MeasureTheory.IsProbabilityMeasure P) (A : BatchAlg d Ω),
          (A.numQueries : ℝ) ≤
            C * ε ^ (-(max ((d : ℝ) - 1) (2 * ν / (2 * ν - 1)))) * (1 + Real.log (1 / ε)) ^ k *
              (1 + Real.log (1 / ρ)) ^ k ∧
          (A.rounds : ℝ) ≤ C * (1 + Real.log (1 / ε)) ∧
          ∀ f : EuclideanSpace ℝ (Fin d) → ℝ, HolderClass p β L f → (∀ y, f x₀ - f y ≤ Δ) →
            ∃ T : Set Ω, MeasurableSet T ∧ 1 - ρ ≤ P.real T ∧
              ∀ ω ∈ T, ‖gradient f (A.run (gradient f) ω)‖ ≤ ε) ∧
      (∃ A : BatchAlg d Unit,
        (A.numQueries : ℝ) ≤
          C * ε ^ (-(max (((d : ℝ) - 1) / ν) (1 / (ν - 1)))) * (1 + Real.log (1 / ε)) ^ k ∧
        (A.rounds : ℝ) ≤ C * (1 + Real.log (1 / ε)) ∧
        ∀ f : EuclideanSpace ℝ (Fin d) → ℝ, HolderClass p β L f →
          A.run (gradient f) () ∈ GeomDRSub.cube d ∧
            ∀ γ : ℝ, 0 < γ → ‖projGrad f γ (A.run (gradient f) ())‖ ≤ ε) ∧
      (∀ ρ : ℝ, 0 < ρ → ρ < 1 →
        ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : MeasureTheory.Measure Ω)
          (_ : MeasureTheory.IsProbabilityMeasure P) (A : BatchAlg d Ω),
          (A.numQueries : ℝ) ≤
            C * ε ^ (-(max (((d : ℝ) - 1) / ν) (2 / (2 * ν - 1)))) * (1 + Real.log (1 / ε)) ^ k *
              (1 + Real.log (1 / ρ)) ^ k ∧
          (A.rounds : ℝ) ≤ C * (1 + Real.log (1 / ε)) ∧
          ∀ f : EuclideanSpace ℝ (Fin d) → ℝ, HolderClass p β L f →
            ∃ T : Set Ω, MeasurableSet T ∧ 1 - ρ ≤ P.real T ∧
              ∀ ω ∈ T, A.run (gradient f) ω ∈ GeomDRSub.cube d ∧
                ∀ γ : ℝ, 0 < γ → ‖projGrad f γ (A.run (gradient f) ω)‖ ≤ ε) := by sorry

end HOTrap
