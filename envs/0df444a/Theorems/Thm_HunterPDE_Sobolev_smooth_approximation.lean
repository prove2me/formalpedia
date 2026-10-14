-- Prove2me | Theorems.Thm_HunterPDE_Sobolev_smooth_approximation
-- name    : HunterPDE.Sobolev.smooth_approximation
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-10T22:16:43.439132+00:00
-- url     : https://prove2.me/theorems/d9607d15-38d8-4836-af57-fc16d4f008f5
-- title:
--   Smooth approximation in the weak-derivative Sobolev norm
-- statement:
--   For every nonnegative integer $k$, every $1\le p<\infty$, and every $f\in W^{k,p}(\mathbb R^n)$, a globally smooth function $g\in W^{k,p}(\mathbb R^n)$ can approximate $f$ within any positive tolerance in the norm of Definition 3.23:
--
--   $$\|f-g\|_{W^{k,p}(\mathbb R^n)}<\varepsilon.$$
--
--   This is the first step of Hunter's proof of Theorem 3.24: convolution with a standard mollifier is smooth, its weak derivatives are the convolutions of the weak derivatives of $f$, and these converge in $L^p$. Compact support is not required of $g$. The order-zero case is included, and tolerances are positive extended reals.
-- source:
--   John K. Hunter, Notes on Partial Differential Equations, revised 6/18/2014, https://www.math.ucdavis.edu/~hunter/pdes/pde_notes.pdf, printed pp. 58–60, Definition 3.23 and proof of Theorem 3.24.

import Definitions.Def_HunterPDE_Sobolev_SobolevSpace

open MeasureTheory
open HunterPDE.Sobolev

theorem HunterPDE.Sobolev.smooth_approximation {n k : ℕ}
    {p : ENNReal} (hp : 1 ≤ p) (hptop : p ≠ ⊤)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : MemW k p Set.univ f)
    (ε : ENNReal) (hε : 0 < ε) :
    ∃ g : EuclideanSpace ℝ (Fin n) → ℝ,
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g ∧ MemW k p Set.univ g ∧
        sobolevNorm k p Set.univ (f - g) < ε := by sorry
