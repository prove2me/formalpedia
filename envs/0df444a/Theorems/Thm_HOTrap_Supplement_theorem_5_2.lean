-- Prove2me | Theorems.Thm_HOTrap_Supplement_theorem_5_2
-- name    : HOTrap.Supplement.theorem_5_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T04:31:15.891516+00:00
-- url     : https://prove2.me/theorems/2d66a635-de73-4541-b91a-9a8046486fd6
-- title:
--   Theorem 5.2 — lazy trapping or descent
-- statement:
--   Under the assumptions and output guarantees of Theorem 5.1, lazy phase-wise reconstruction gives deterministic total bounds
--   $$
--   O_{p,\beta_p}\!\left(d^p+d^{p-1+\beta_p/(\nu-1)}L_p^{1/(\nu-1)}\Delta\varepsilon^{-\nu/(\nu-1)}\right)
--   $$
--   for strict function values and
--   $$
--   O_{p,\beta_p}\!\left(d^{p-1}+d^{p-2+\beta_p/(\nu-1)}L_p^{1/(\nu-1)}\Delta\varepsilon^{-\nu/(\nu-1)}\right)
--   $$
--   for strict gradients.
--
--   The algorithms retain both domains and output guarantees of Theorem 5.1 and make no query and return $x^0$ when $\Delta=0$. The theorem does not repeat Theorem 5.1's query-location sentence for the lazy implementation.
--
--   Differences from the source:
--   - encoding: $O_{p,\beta_p}$ notation → one positive constant quantified before $d,L_p,\Delta,\varepsilon$; reason: this is exactly dependence only on $p,\beta_p$
--   - encoding: the phrase “same output guarantees” → the unconstrained and cube outputs and the $\Delta=0$ zero-query boundary clause are repeated explicitly; reason: Lean records inherited clauses rather than referring to prose
--   - encoding: $f(x^0)-\inf_{y\in X}f(y)\le\Delta$ → $f(x^0)-f(y)\le\Delta$ for every $y\in X$; reason: equivalent on the relevant nonempty domain and avoids a default-valued real infimum
--   - encoding: strict value-only and gradient-only algorithms on $\mathbb R^d$ → response-typed fixed-budget structures on `EuclideanSpace ℝ (Fin d)`; reason: the response type excludes the other oracle component, zero-based coordinates preserve Euclidean geometry, and shorter runs may be padded
-- source:
--   Zhou–Sugiyama–Suzuki, Finding Stationary Points under Higher-Order Smoothness: Trapping Algorithms and First-Order Lower Bounds, arXiv:2610.02791, Theorem 5.2, p.28

import Mathlib
import Definitions.Def_GeomDRSub_cube
import Definitions.Def_HOTrap_HolderClass
import Definitions.Def_HOTrap_projGrad
import Definitions.Def_HOTrap_Supplement_StrictBatchAlg

namespace HOTrap.Supplement

/-- **Theorem 5.2 (lazy trapping or descent).** Zhou--Sugiyama--Suzuki, *Finding Stationary
Points under Higher-Order Smoothness: Trapping Algorithms and First-Order Lower Bounds*,
arXiv:2610.02791, Theorem 5.2, p.28.

The lazy implementations retain the output guarantees of Theorem 5.1 and improve the repeated
powers of the dimension to the two powers printed in Theorem 5.2.

**Formalization Note.** `C` depends only on `p,β`.  The four clauses separately expose the two
strict oracle types and the unconstrained/cube domains.  The inherited output and zero-query
`Δ=0` clauses are explicit rather than hidden in a reference to Theorem 5.1.  Unlike Theorem 5.1,
Theorem 5.2 does not say that the lazy implementation's queries lie in `X`; Appendix D places the
cube queries in an enlarged neighborhood. -/
theorem theorem_5_2 (p : ℕ) (hp : 1 ≤ p) (β : ℝ) (hβ0 : 0 < β) (hβ1 : β ≤ 1) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (d : ℕ) (hd : 1 ≤ d) (L Δ ε ν : ℝ), 0 ≤ L → 0 ≤ Δ → 0 < ε →
        ν = (p : ℝ) + β →
        ∀ x₀ : EuclideanSpace ℝ (Fin d),
          (∃ A : StrictBatchAlg d ℝ Unit,
            (A.numQueries : ℝ) ≤ C *
              ((d : ℝ) ^ p +
                Real.rpow (d : ℝ) ((p : ℝ) - 1 + β / (ν - 1)) *
                  Real.rpow L (1 / (ν - 1)) * Δ * Real.rpow ε (-ν / (ν - 1))) ∧
            ∀ f : EuclideanSpace ℝ (Fin d) → ℝ, HOTrap.HolderClass p β L f →
              (∀ x, 0 ≤ f x) → (∀ y, f x₀ - f y ≤ Δ) →
              ‖gradient f (A.run f ())‖ ≤ ε ∧
                (Δ = 0 → A.numQueries = 0 ∧ A.run f () = x₀)) ∧
          (∃ A : StrictBatchAlg d (EuclideanSpace ℝ (Fin d)) Unit,
            (A.numQueries : ℝ) ≤ C *
              ((d : ℝ) ^ (p - 1) +
                Real.rpow (d : ℝ) ((p : ℝ) - 2 + β / (ν - 1)) *
                  Real.rpow L (1 / (ν - 1)) * Δ * Real.rpow ε (-ν / (ν - 1))) ∧
            ∀ f : EuclideanSpace ℝ (Fin d) → ℝ, HOTrap.HolderClass p β L f →
              (∀ x, 0 ≤ f x) → (∀ y, f x₀ - f y ≤ Δ) →
              ‖gradient f (A.run (gradient f) ())‖ ≤ ε ∧
                (Δ = 0 → A.numQueries = 0 ∧ A.run (gradient f) () = x₀)) ∧
          (∃ A : StrictBatchAlg d ℝ Unit,
            (A.numQueries : ℝ) ≤ C *
              ((d : ℝ) ^ p +
                Real.rpow (d : ℝ) ((p : ℝ) - 1 + β / (ν - 1)) *
                  Real.rpow L (1 / (ν - 1)) * Δ * Real.rpow ε (-ν / (ν - 1))) ∧
            ∀ f : EuclideanSpace ℝ (Fin d) → ℝ, HOTrap.HolderClass p β L f →
              (∀ y ∈ GeomDRSub.cube d, f x₀ - f y ≤ Δ) →
              x₀ ∈ GeomDRSub.cube d →
              A.run f () ∈ GeomDRSub.cube d ∧
              (∀ γ : ℝ, 0 < γ → ‖HOTrap.projGrad f γ (A.run f ())‖ ≤ ε) ∧
              (Δ = 0 → A.numQueries = 0 ∧ A.run f () = x₀)) ∧
          (∃ A : StrictBatchAlg d (EuclideanSpace ℝ (Fin d)) Unit,
            (A.numQueries : ℝ) ≤ C *
              ((d : ℝ) ^ (p - 1) +
                Real.rpow (d : ℝ) ((p : ℝ) - 2 + β / (ν - 1)) *
                  Real.rpow L (1 / (ν - 1)) * Δ * Real.rpow ε (-ν / (ν - 1))) ∧
            ∀ f : EuclideanSpace ℝ (Fin d) → ℝ, HOTrap.HolderClass p β L f →
              (∀ y ∈ GeomDRSub.cube d, f x₀ - f y ≤ Δ) →
              x₀ ∈ GeomDRSub.cube d →
              A.run (gradient f) () ∈ GeomDRSub.cube d ∧
              (∀ γ : ℝ, 0 < γ →
                ‖HOTrap.projGrad f γ (A.run (gradient f) ())‖ ≤ ε) ∧
              (Δ = 0 → A.numQueries = 0 ∧ A.run (gradient f) () = x₀)) := by sorry

end HOTrap.Supplement
