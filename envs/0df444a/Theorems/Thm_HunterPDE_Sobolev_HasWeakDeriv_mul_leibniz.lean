-- Prove2me | Theorems.Thm_HunterPDE_Sobolev_HasWeakDeriv_mul_leibniz
-- name    : HunterPDE.Sobolev.HasWeakDeriv.mul_leibniz
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-11T22:00:49.155853+00:00
-- url     : https://prove2.me/theorems/c982c178-8de2-4067-84bd-83317f8b580e
-- title:
--   Higher weak Leibniz formula for a smooth multiplier on an open domain
-- statement:
--   Let $\Omega\subseteq\mathbb R^n$ be open and suppose $d_\beta$ represents the locally integrable weak derivative $D^\beta f$ for every $|\beta|\le k$. If $\eta$ is smooth on $\mathbb R^n$, then for every $|\alpha|\le k$ the explicitly defined function
--
--   $$g_\alpha(x)=\sum_{|\beta|\le k}\left(\prod_{i=1}^n {\alpha_i\choose\beta_i}\right)D^{\alpha-\beta}\eta(x)\,d_\beta(x)$$
--
--   is locally integrable on $\Omega$ and represents $D^\alpha(\eta f)$. Subtraction of multi-indices is componentwise truncated subtraction; a binomial coefficient is zero when $\beta_i>\alpha_i$, so precisely the usual Leibniz terms contribute. There is no global integrability or boundedness assumption on the multiplier, and dimension and order zero are included.
-- source:
--   John K. Hunter, Notes on Partial Differential Equations, revised 6/18/2014, https://www.math.ucdavis.edu/~hunter/pdes/pde_notes.pdf, Propositions 3.16 and 3.17, printed p. 54. The displayed higher-order formula is the iterated consequence of the first-order smooth weak product rule and commutation of weak derivatives, rather than a verbatim statement in the source.

import Definitions.Def_HunterPDE_Sobolev_SobolevSpace
import Mathlib.Data.Nat.Choose.Basic

open MeasureTheory HunterPDE.Sobolev

theorem HunterPDE.Sobolev.HasWeakDeriv.mul_leibniz {n k : ℕ}
    (Ω : Set (EuclideanSpace ℝ (Fin n))) (hΩ : IsOpen Ω)
    (f η : EuclideanSpace ℝ (Fin n) → ℝ)
    (d : (Fin n → ℕ) → EuclideanSpace ℝ (Fin n) → ℝ)
    (hd : ∀ β, ∑ i, β i ≤ k → HasWeakDeriv Ω β f (d β))
    (hη : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) η)
    (α : Fin n → ℕ) (hα : ∑ i, α i ≤ k) :
    HasWeakDeriv Ω α (fun x => η x * f x)
      (fun x => ∑ β ∈ multiIndices n k,
        (∏ i, (Nat.choose (α i) (β i) : ℝ)) *
          iteratedPartial (fun i => α i - β i) η x * d β x) := by sorry
