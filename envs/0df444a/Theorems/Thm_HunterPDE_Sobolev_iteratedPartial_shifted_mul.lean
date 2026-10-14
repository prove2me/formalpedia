-- Prove2me | Theorems.Thm_HunterPDE_Sobolev_iteratedPartial_shifted_mul
-- name    : HunterPDE.Sobolev.iteratedPartial_shifted_mul
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-12T14:34:49.791253+00:00
-- url     : https://prove2.me/theorems/c0f8b722-2d60-48b8-8a0e-73387c13660f
-- title:
--   Shifted higher product rule for smooth coordinate derivatives
-- statement:
--   Let η and φ be globally C∞ real functions on Euclidean n-space, and let δ and β be arbitrary multi-indices. For any finite set S containing every coordinatewise sub-index of β, the βth derivative of (D^δ η)φ equals the sum over γ in S of the multi-index binomial coefficient times D^(δ+(β−γ)) η times D^γ φ, evaluated at the same point. Additional indices in S contribute zero. The coordinate derivatives are composed in the order fixed by the Sobolev definition; global smoothness permits commuting mixed partial derivatives. This is the ordinary higher product rule with an arbitrary initial derivative shift, and has no weak-derivative or measure assumptions.
-- source:
--   John K. Hunter, Notes on Partial Differential Equations, revised 6/18/2014, https://www.math.ucdavis.edu/~hunter/pdes/pde_notes.pdf, §1.8 printed p. 10 (multi-index notation), and Proposition 3.16 proof, printed p. 54 (smooth product rule). The shifted higher formula is a derived consequence of iterating the product rule and commuting smooth mixed partials, not a verbatim source statement.

import Definitions.Def_HunterPDE_Sobolev_SobolevSpace
import Mathlib.Data.Nat.Choose.Basic

open HunterPDE.Sobolev

theorem HunterPDE.Sobolev.iteratedPartial_shifted_mul {n : ℕ}
    (η φ : EuclideanSpace ℝ (Fin n) → ℝ)
    (hη : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) η)
    (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ)
    (δ β : Fin n → ℕ) (s : Finset (Fin n → ℕ))
    (hs : ∀ γ : Fin n → ℕ, (∀ i, γ i ≤ β i) → γ ∈ s)
    (x : EuclideanSpace ℝ (Fin n)) :
    iteratedPartial β (fun y => iteratedPartial δ η y * φ y) x =
      ∑ γ ∈ s, (∏ i, (Nat.choose (β i) (γ i) : ℝ)) *
        (iteratedPartial (fun i => δ i + (β i - γ i)) η x *
          iteratedPartial γ φ x) := by sorry
