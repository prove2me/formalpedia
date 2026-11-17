-- Prove2me | Theorems.Thm_HOTrap_Supplement_theorem_3_1
-- name    : HOTrap.Supplement.theorem_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T04:29:59.526125+00:00
-- url     : https://prove2.me/theorems/ba16a4ad-fb96-4ef2-a484-f4b2e6df9b5e
-- title:
--   Theorem 3.1 — $p$th-order trapping from function values
-- statement:
--   Fix $d\ge2$, $p\ge1$, $\beta_p\in(0,1]$, and let $\nu=p+\beta_p$. For every $f\in C^{p,\beta_p}(L_p)$ and every $\varepsilon>0$, there is a deterministic strict value-only trapping algorithm using $O(\log(1/\varepsilon))$ adaptive rounds such that:
--
--   1. In the unconstrained problem with the known lower bound $f\ge0$, given $x^0$ and $\Delta$ with $f(x^0)-\inf f\le\Delta$, it returns $z$ with $\lVert\nabla f(z)\rVert_2\le\varepsilon$ and uses $O(\varepsilon^{-(d-1)})$ value queries per round.
--   2. On $[0,1]^d$, for a fixed $\gamma>0$, it returns $z\in[0,1]^d$ with $\lVert G_\gamma(z)\rVert_2\le\varepsilon$ and uses $O(\varepsilon^{-(d-1)/\nu})$ value queries per round.
--
--   The algorithm receives exact function values only; it has no gradient, mixed, or higher-derivative oracle.
--
--   Differences from the source:
--   - encoding: asymptotic $O(\varepsilon^{-a})$ and $O(\log(1/\varepsilon))$ bounds for $\varepsilon>0$ → explicit uniform constants with $\max\{1,\varepsilon^{-a}\}$ and $1+\max\{0,\log(1/\varepsilon)\}$; reason: this extends the same small-$\varepsilon$ asymptotics to all positive accuracies without a negative round bound
--   - encoding: $d=\Theta(1)$ → $d$ is fixed before the complexity constant and satisfies $d\ge2$; reason: quantifier order is the formal content of fixed dimension
--   - encoding: $f(x^0)-\inf f\le\Delta$ → $f(x^0)-f(y)\le\Delta$ for every $y$; reason: equivalent for lower-bounded $f$ and avoids the junk value of a real infimum
--   - encoding: $\mathbb R^d$ with exact value-only adaptive rounds → `EuclideanSpace ℝ (Fin d)` and a response-typed fixed-budget batched structure; reason: zero-based finite coordinates preserve Euclidean geometry, and shorter executions can be padded without changing oracle power
-- source:
--   Zhou–Sugiyama–Suzuki, Finding Stationary Points under Higher-Order Smoothness: Trapping Algorithms and First-Order Lower Bounds, arXiv:2610.02791, Theorem 3.1, p.14

import Mathlib
import Definitions.Def_GeomDRSub_cube
import Definitions.Def_HOTrap_HolderClass
import Definitions.Def_HOTrap_projGrad
import Definitions.Def_HOTrap_Supplement_StrictBatchAlg

namespace HOTrap.Supplement

/-- **Theorem 3.1 (p-th order trapping via function value oracle).**
Zhou--Sugiyama--Suzuki, *Finding Stationary Points under Higher-Order Smoothness: Trapping
Algorithms and First-Order Lower Bounds*, arXiv:2610.02791, Theorem 3.1, p.14.

For fixed `d ≥ 2`, a deterministic strict value-only algorithm uses logarithmically many adaptive
rounds and `O(ε^{-(d-1)})` queries per round in the lower-bounded unconstrained problem, or
`O(ε^{-(d-1)/(p+β)})` queries per round on the cube, and returns the stated stationary/KKT point.

**Formalization Note.** `C` may depend on the fixed `d,p,β,L,Δ,γ`, but not on `ε`, the objective,
or its answers.  `max 1` and `1 + max 0 log(1/ε)` extend the asymptotic bounds harmlessly to all
`ε > 0`.  The unconstrained lower-bound/gap convention is written shift-invariantly as
`∀ y, f x₀ - f y ≤ Δ`.  The cube's `ε`-stationarity is the fixed-`γ` KKT convention of Section 2.
The response type `ℝ` prevents the algorithm from seeing gradients or higher derivatives. -/
theorem theorem_3_1 (d p : ℕ) (hd : 2 ≤ d) (hp : 1 ≤ p) (β L Δ γ ν : ℝ)
    (hβ0 : 0 < β) (hβ1 : β ≤ 1) (hL : 0 ≤ L) (hΔ : 0 < Δ) (hγ : 0 < γ)
    (hν : ν = (p : ℝ) + β) :
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε →
      (∀ x₀ : EuclideanSpace ℝ (Fin d),
        ∃ A : StrictBatchAlg d ℝ Unit,
          (∀ r < A.rounds,
            (A.batch r : ℝ) ≤ C * max 1 (Real.rpow ε (-((d : ℝ) - 1)))) ∧
          (A.rounds : ℝ) ≤ C * (1 + max 0 (Real.log (1 / ε))) ∧
          ∀ f : EuclideanSpace ℝ (Fin d) → ℝ, HOTrap.HolderClass p β L f →
            (∀ x, 0 ≤ f x) → (∀ y, f x₀ - f y ≤ Δ) →
            ‖gradient f (A.run f ())‖ ≤ ε) ∧
      (∃ A : StrictBatchAlg d ℝ Unit,
        (∀ r < A.rounds,
          (A.batch r : ℝ) ≤
            C * max 1 (Real.rpow ε (-(((d : ℝ) - 1) / ν)))) ∧
        (A.rounds : ℝ) ≤ C * (1 + max 0 (Real.log (1 / ε))) ∧
        ∀ f : EuclideanSpace ℝ (Fin d) → ℝ, HOTrap.HolderClass p β L f →
          A.run f () ∈ GeomDRSub.cube d ∧ ‖HOTrap.projGrad f γ (A.run f ())‖ ≤ ε) := by sorry

end HOTrap.Supplement
