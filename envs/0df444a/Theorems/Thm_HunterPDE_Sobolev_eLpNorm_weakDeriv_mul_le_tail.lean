-- Prove2me | Theorems.Thm_HunterPDE_Sobolev_eLpNorm_weakDeriv_mul_le_tail
-- name    : HunterPDE.Sobolev.eLpNorm_weakDeriv_mul_le_tail
-- status  : Open
-- author  : @Mazecto
-- created : 2026-10-10T23:12:18.944461+00:00
-- url     : https://prove2.me/theorems/9ff5f499-f2ff-41a2-805b-d028fa793a3a
-- title:
--   Weak Sobolev multiplier estimate by exterior derivative tails
-- statement:
--   Let $k\ge0$, $1\le p\le\infty$, and let $d_\beta\in L^p(\mathbb R^n)$ be weak derivatives of a locally integrable function $f$ for every $|\beta|\le k$. Let $\eta$ be smooth, vanish on $\{x:|x|<R\}$, and satisfy $|D^\beta\eta(x)|\le C$ for all these orders and all $x$, where $C\ge0$. Then, for every $|\alpha|\le k$,
--
--   $$\|D^\alpha(\eta f)\|_{L^p}\le 2^k C\sum_{|\beta|\le k}\|d_\beta\|_{L^p(\{x:|x|\ge R\})}.$$
--
--   The derivative on the left uses the chosen weak representative. The intended proof establishes the weak Leibniz formula, uses almost-everywhere uniqueness, and bounds its binomial coefficients by their total mass $2^{|\alpha|}\le2^k$. Each derivative of the multiplier vanishes inside the ball. This estimate localizes Sobolev errors without assuming that $f$ is smooth. It includes order and dimension zero, arbitrary real $R$, and the exponent infinity. This is an independent open analytic obligation.
-- source:
--   John K. Hunter, Notes on Partial Differential Equations (revised 6/18/2014), https://www.math.ucdavis.edu/~hunter/pdes/pde_notes.pdf, Proposition 3.16 (weak product rule), Proposition 3.17 (commuting weak derivatives), printed p. 54, and the cutoff argument in Theorem 3.24, printed p. 59. The displayed estimate is a quantitative generalization derived from repeated Leibniz and the Lp triangle inequality; it is not quoted verbatim from the source.

import Definitions.Def_HunterPDE_Sobolev_SobolevSpace

open MeasureTheory HunterPDE.Sobolev

theorem HunterPDE.Sobolev.eLpNorm_weakDeriv_mul_le_tail {n k : ℕ} {p : ENNReal}
    (hp : 1 ≤ p) (f η : EuclideanSpace ℝ (Fin n) → ℝ)
    (d : (Fin n → ℕ) → EuclideanSpace ℝ (Fin n) → ℝ)
    (hd : ∀ β, ∑ i, β i ≤ k → HasWeakDeriv Set.univ β f (d β) ∧ MemLp (d β) p volume)
    (hη : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) η)
    (R C : ℝ) (hC : 0 ≤ C)
    (hzero : ∀ x, ‖x‖ < R → η x = 0)
    (hbound : ∀ β, ∑ i, β i ≤ k → ∀ x, ‖iteratedPartial β η x‖ ≤ C)
    (α : Fin n → ℕ) (hα : ∑ i, α i ≤ k) :
    eLpNorm (weakDeriv Set.univ α (fun x => η x * f x)) p volume ≤
      (2 : ENNReal) ^ k * ENNReal.ofReal C *
        ∑ β ∈ multiIndices n k, eLpNorm (d β) p (volume.restrict {x | R ≤ ‖x‖}) := by sorry
