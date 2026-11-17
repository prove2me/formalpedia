-- Prove2me | Theorems.Thm_HOTrap_Supplement_theorem_5_1
-- name    : HOTrap.Supplement.theorem_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T04:30:36.569079+00:00
-- url     : https://prove2.me/theorems/048edf6b-d531-4ad7-979f-387e5e04793c
-- title:
--   Theorem 5.1 — trapping or descent with strict low-order oracles
-- statement:
--   Let $p\ge1$, $\beta_p\in(0,1]$, and $\nu=p+\beta_p$. In the unconstrained case let $f\in C^{p,\beta_p}(L_p)$ be nonnegative with $f(x^0)-\inf_{\mathbb R^d} f\le\Delta$; in the cube case let $x^0\in X=[0,1]^d$ and $f(x^0)-\min_X f\le\Delta$. In arbitrary dimension, deterministic trapping-or-descent algorithms have the following total query bounds:
--   $$
--   O_{p,\beta_p}\!\left(d^p\left[1+L_p^{1/(\nu-1)}\Delta\varepsilon^{-\nu/(\nu-1)}\right]\right)
--   $$
--   for the strict value-only oracle, and
--   $$
--   O_{p,\beta_p}\!\left(d^{p-1}\left[1+L_p^{1/(\nu-1)}\Delta\varepsilon^{-\nu/(\nu-1)}\right]\right)
--   $$
--   for the strict gradient-only oracle.
--
--   For $X=\mathbb R^d$ the output satisfies $\lVert\nabla f(z)\rVert_2\le\varepsilon$. For $X=[0,1]^d$ the output lies in $X$ and satisfies $\lVert G_\gamma(z)\rVert_2\le\varepsilon$ for every $\gamma>0$. Every query lies in $X$. If $\Delta=0$, both oracle implementations make no queries and return $x^0$.
--
--   Differences from the source:
--   - encoding: $O_{p,\beta_p}$ notation → one positive constant quantified before $d,L_p,\Delta,\varepsilon$; reason: this is exactly dependence only on $p,\beta_p$
--   - encoding: $f(x^0)-\inf_{y\in X}f(y)\le\Delta$ → $f(x^0)-f(y)\le\Delta$ for every $y\in X$; reason: equivalent on the relevant nonempty domain and avoids a default-valued real infimum
--   - encoding: strict value-only and gradient-only algorithms on $\mathbb R^d$ → response-typed fixed-budget structures on `EuclideanSpace ℝ (Fin d)`; reason: the response type excludes the other oracle component, zero-based coordinates preserve Euclidean geometry, and shorter runs may be padded
-- source:
--   Zhou–Sugiyama–Suzuki, Finding Stationary Points under Higher-Order Smoothness: Trapping Algorithms and First-Order Lower Bounds, arXiv:2610.02791, Theorem 5.1, pp.27–28

import Mathlib
import Definitions.Def_GeomDRSub_cube
import Definitions.Def_HOTrap_HolderClass
import Definitions.Def_HOTrap_projGrad
import Definitions.Def_HOTrap_Supplement_StrictBatchAlg

namespace HOTrap.Supplement

/-- **Theorem 5.1 (trapping or descent).** Zhou--Sugiyama--Suzuki, *Finding Stationary
Points under Higher-Order Smoothness: Trapping Algorithms and First-Order Lower Bounds*,
arXiv:2610.02791, Theorem 5.1, pp.27--28.

The theorem gives, in arbitrary dimension, both the strict value-only and strict gradient-only
deterministic algorithms, on `ℝ^d` and on `[0,1]^d`, with the exact printed dependence on
`d,L_p,Δ,ε`.  Cube queries stay in the cube; if `Δ=0`, every algorithm makes no query and returns
`x₀`.

**Formalization Note.** The universal constant `C` occurs before `d,L,Δ,ε` and therefore depends
only on `p,β`, exactly as `O_{p,β}` requires.  Global nonnegativity is the paper's known lower-bound
zero convention for the unconstrained clauses.  In the cube clauses the gap is instead relative to
the minimum on the cube, as made explicit in Appendix D.  A value algorithm has response type
`ℝ`; a gradient algorithm has response type `ℝ^d`, so neither can access the other oracle
component. -/
theorem theorem_5_1 (p : ℕ) (hp : 1 ≤ p) (β : ℝ) (hβ0 : 0 < β) (hβ1 : β ≤ 1) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (d : ℕ) (hd : 1 ≤ d) (L Δ ε ν : ℝ), 0 ≤ L → 0 ≤ Δ → 0 < ε →
        ν = (p : ℝ) + β →
        ∀ x₀ : EuclideanSpace ℝ (Fin d),
          (∃ A : StrictBatchAlg d ℝ Unit,
            (A.numQueries : ℝ) ≤
              C * (d : ℝ) ^ p *
                (1 + Real.rpow L (1 / (ν - 1)) * Δ * Real.rpow ε (-ν / (ν - 1))) ∧
            ∀ f : EuclideanSpace ℝ (Fin d) → ℝ, HOTrap.HolderClass p β L f →
              (∀ x, 0 ≤ f x) → (∀ y, f x₀ - f y ≤ Δ) →
              ‖gradient f (A.run f ())‖ ≤ ε ∧
                (Δ = 0 → A.numQueries = 0 ∧ A.run f () = x₀)) ∧
          (∃ A : StrictBatchAlg d (EuclideanSpace ℝ (Fin d)) Unit,
            (A.numQueries : ℝ) ≤
              C * (d : ℝ) ^ (p - 1) *
                (1 + Real.rpow L (1 / (ν - 1)) * Δ * Real.rpow ε (-ν / (ν - 1))) ∧
            ∀ f : EuclideanSpace ℝ (Fin d) → ℝ, HOTrap.HolderClass p β L f →
              (∀ x, 0 ≤ f x) → (∀ y, f x₀ - f y ≤ Δ) →
              ‖gradient f (A.run (gradient f) ())‖ ≤ ε ∧
                (Δ = 0 → A.numQueries = 0 ∧ A.run (gradient f) () = x₀)) ∧
          (∃ A : StrictBatchAlg d ℝ Unit,
            (A.numQueries : ℝ) ≤
              C * (d : ℝ) ^ p *
                (1 + Real.rpow L (1 / (ν - 1)) * Δ * Real.rpow ε (-ν / (ν - 1))) ∧
            ∀ f : EuclideanSpace ℝ (Fin d) → ℝ, HOTrap.HolderClass p β L f →
              (∀ y ∈ GeomDRSub.cube d, f x₀ - f y ≤ Δ) →
              x₀ ∈ GeomDRSub.cube d →
              (∀ r < A.rounds, ∀ i,
                A.query r () (A.answers f () r) i ∈ GeomDRSub.cube d) ∧
              A.run f () ∈ GeomDRSub.cube d ∧
              (∀ γ : ℝ, 0 < γ → ‖HOTrap.projGrad f γ (A.run f ())‖ ≤ ε) ∧
              (Δ = 0 → A.numQueries = 0 ∧ A.run f () = x₀)) ∧
          (∃ A : StrictBatchAlg d (EuclideanSpace ℝ (Fin d)) Unit,
            (A.numQueries : ℝ) ≤
              C * (d : ℝ) ^ (p - 1) *
                (1 + Real.rpow L (1 / (ν - 1)) * Δ * Real.rpow ε (-ν / (ν - 1))) ∧
            ∀ f : EuclideanSpace ℝ (Fin d) → ℝ, HOTrap.HolderClass p β L f →
              (∀ y ∈ GeomDRSub.cube d, f x₀ - f y ≤ Δ) →
              x₀ ∈ GeomDRSub.cube d →
              (∀ r < A.rounds, ∀ i,
                A.query r () (A.answers (gradient f) () r) i ∈ GeomDRSub.cube d) ∧
              A.run (gradient f) () ∈ GeomDRSub.cube d ∧
              (∀ γ : ℝ, 0 < γ →
                ‖HOTrap.projGrad f γ (A.run (gradient f) ())‖ ≤ ε) ∧
              (Δ = 0 → A.numQueries = 0 ∧ A.run (gradient f) () = x₀)) := by sorry

end HOTrap.Supplement
