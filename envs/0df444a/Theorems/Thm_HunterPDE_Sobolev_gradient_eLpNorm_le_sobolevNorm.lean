-- Prove2me | Theorems.Thm_HunterPDE_Sobolev_gradient_eLpNorm_le_sobolevNorm
-- name    : HunterPDE.Sobolev.gradient_eLpNorm_le_sobolevNorm
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-14T21:15:42.623671+00:00
-- url     : https://prove2.me/theorems/f5199f59-1790-4855-b343-0b4961ea1768
-- title:
--   Gradient Lp norm controlled by the multi-index Sobolev norm
-- statement:
--   For every compactly supported smooth real-valued function on Euclidean n-space and every real p at least 1, the Lp norm of the Euclidean gradient is at most n times the multi-index W^{1,p} norm. The dimension factor is independent of the function. This follows by decomposing the gradient into coordinate vectors, identifying classical coordinate derivatives with the chosen weak derivatives almost everywhere, bounding each coordinate Lp norm by its summand in the Sobolev norm, and applying finite-sum Minkowski. No restriction p<n is required; the assertion also covers dimension zero.
-- source:
--   Hunter, Notes on PDEs (revised 6/18/2014), https://www.math.ucdavis.edu/~hunter/pdes/ch3.pdf, Definition 3.23 p. 58 and norm comparison used in Theorem 3.31 pp. 66–67; the dimension-dependent estimate is an explicit finite-dimensional comparison for the multi-index norm.

import Definitions.Def_HunterPDE_Sobolev_SobolevSpace
import Mathlib.Analysis.Calculus.Gradient.Basic
open MeasureTheory HunterPDE.Sobolev

theorem HunterPDE.Sobolev.gradient_eLpNorm_le_sobolevNorm {n : ℕ} {p : ℝ}
    (hp : 1 ≤ p) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : IsTestFunction Set.univ f) :
    eLpNorm (fun x => ‖gradient f x‖) (ENNReal.ofReal p) volume ≤
      (n : ENNReal) * sobolevNorm 1 (ENNReal.ofReal p) Set.univ f := by sorry
