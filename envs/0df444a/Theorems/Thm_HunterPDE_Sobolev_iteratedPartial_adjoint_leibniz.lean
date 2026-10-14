-- Prove2me | Theorems.Thm_HunterPDE_Sobolev_iteratedPartial_adjoint_leibniz
-- name    : HunterPDE.Sobolev.iteratedPartial_adjoint_leibniz
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-11T22:16:15.287987+00:00
-- url     : https://prove2.me/theorems/0b47c8f6-fa42-4a0c-9a12-e85a84d25367
-- title:
--   Signed higher Leibniz cancellation for smooth functions
-- statement:
--   For globally smooth real functions $η$ and $φ$ on $ℝ^n$ and a multi-index $|α|≤k$, the signed differentiated product sum satisfies
--
--   $$\sum_{|β|≤k} {α\choose β}(-1)^{|β|}D^β((D^{α-β}η)φ)=(-1)^{|α|}η D^αφ.$$
--
--   The binomial coefficient is the product of coordinate binomial coefficients. Multi-index subtraction is truncated; coefficients outside $β≤α$ vanish. No support or integration hypotheses are needed. Dimension zero and order zero are included. This identity is the classical cancellation underlying multiplication of distributions by smooth functions.
-- source:
--   John K. Hunter, Notes on Partial Differential Equations, revised 6/18/2014, https://www.math.ucdavis.edu/~hunter/pdes/pde_notes.pdf, §1.8 printed p. 10 (multi-index calculus) and Proposition 3.16 proof, printed p. 54. The signed higher identity is a derived algebraic consequence of the smooth product rule: expand each differentiated product and apply binomial cancellation coordinatewise; it is not a verbatim source statement.

import Definitions.Def_HunterPDE_Sobolev_SobolevSpace
import Mathlib.Data.Nat.Choose.Basic

open HunterPDE.Sobolev

theorem HunterPDE.Sobolev.iteratedPartial_adjoint_leibniz {n k : ℕ}
    (η φ : EuclideanSpace ℝ (Fin n) → ℝ)
    (hη : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) η)
    (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ)
    (α : Fin n → ℕ) (hα : ∑ i, α i ≤ k) (x : EuclideanSpace ℝ (Fin n)) :
    (∑ β ∈ multiIndices n k,
      (∏ i, (Nat.choose (α i) (β i) : ℝ)) * (-1 : ℝ) ^ (∑ i, β i) *
        iteratedPartial β (fun y => iteratedPartial (fun i => α i - β i) η y * φ y) x) =
      (-1 : ℝ) ^ (∑ i, α i) * η x * iteratedPartial α φ x := by sorry
