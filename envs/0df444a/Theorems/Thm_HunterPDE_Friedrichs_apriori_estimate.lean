-- Prove2me | Theorems.Thm_HunterPDE_Friedrichs_apriori_estimate
-- name    : HunterPDE.Friedrichs.apriori_estimate
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T00:56:17.352353+00:00
-- url     : https://prove2.me/theorems/addf49fa-36ca-4ec8-90c2-0193f73286d4
-- title:
--   Theorem 8.6 — a priori estimates c‖u‖ ≤ ‖Lu‖ and c‖v‖ ≤ ‖L*v‖ for smooth functions
-- statement:
--   Let the BVP (8.1) be smooth (Definition 8.1) on a bounded open set $\Omega \subseteq \mathbb{R}^n$ with $C^2$-boundary, with non-characteristic boundary, positive symmetric with constant $c > 0$ (Definition 8.4), and with a maximally positive boundary condition $B_-u = 0$ (Definition 8.5). Let $\|u\| = \left(\int_\Omega |u|^2\,dx\right)^{1/2}$ be the $L^2(\Omega;\mathbb{R}^m)$ norm (8.9). Then
--   $$c\|u\| \le \|Lu\| \quad \text{for } u \in C^1(\overline\Omega),\ B_-u = 0 \text{ on } \partial\Omega, \qquad c\|v\| \le \|L^*v\| \quad \text{for } v \in C^1(\overline\Omega),\ B_+^T v = 0 \text{ on } \partial\Omega .$$
--   These energy estimates for the operator and its adjoint give uniqueness of smooth solutions (Corollary 8.7) and, via the Riesz representation theorem, existence of weak solutions (Theorem 8.9).
--
--   **Formalization Note.** The norms are `eLpNorm · 2 (volume.restrict Ω)` in $[0,\infty]$, so no integrability side condition is hidden, and $c$ enters as `ENNReal.ofReal c`. The constant $c$ is the constant of (8.6), named as an argument of `IsPositiveSymmetric`.
-- source:
--   Hunter, Notes on Partial Differential Equations (revised 6/18/2014), p. 225, Theorem 8.6

import Mathlib
import Definitions.Def_HunterPDE_Friedrichs_BoundaryValueProblem

open MeasureTheory Matrix

namespace HunterPDE.Friedrichs

/-- Hunter, *Notes on PDEs* (revised 6/18/2014), Theorem 8.6, p. 225. Under the smoothness
conditions of Definition 8.1, a non-characteristic boundary (§8.2), the positivity condition (8.6)
of Definition 8.4 with constant `c > 0`, and a maximally positive boundary condition
(Definition 8.5): if `u ∈ C¹(Ω̄)` and `B₋u = 0` on `∂Ω` then `c‖u‖ ≤ ‖Lu‖`, and if `v ∈ C¹(Ω̄)`
and `B₊ᵀv = 0` on `∂Ω` then `c‖v‖ ≤ ‖L*v‖`. Here `‖·‖` is the `L²(Ω; ℝᵐ)` norm (8.9),
`(∫_Ω |u|² dx)^{1/2}` with `|·|` the Euclidean norm, taken in `ℝ≥0∞` (`eLpNorm`). -/
theorem apriori_estimate {n m : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin n)))
    (A : Fin n → EuclideanSpace ℝ (Fin n) → Matrix (Fin m) (Fin m) ℝ)
    (C Bm : EuclideanSpace ℝ (Fin n) → Matrix (Fin m) (Fin m) ℝ) (c : ℝ)
    (hsmooth : IsSmoothBVP Ω A C Bm) (hnc : IsNoncharacteristic Ω A)
    (hpos : IsPositiveSymmetric Ω A C c) (hmax : IsMaximallyPositive Ω A Bm) :
    (∀ u ∈ Dom Ω Bm,
      ENNReal.ofReal c * eLpNorm u 2 (volume.restrict Ω) ≤
        eLpNorm (Lop A C u) 2 (volume.restrict Ω)) ∧
    (∀ v ∈ Dstar Ω A Bm,
      ENNReal.ofReal c * eLpNorm v 2 (volume.restrict Ω) ≤
        eLpNorm (Ladj A C v) 2 (volume.restrict Ω)) := by sorry

end HunterPDE.Friedrichs
