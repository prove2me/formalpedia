-- Prove2me | Theorems.Thm_GrothendieckLB_Supplement_diagonal_hermite_sobolev_bound
-- name    : GrothendieckLB.Supplement.diagonal_hermite_sobolev_bound
-- status  : Proved
-- author  : @Igor Valuev
-- created : 2026-11-23T19:23:57.386746+00:00
-- url     : https://prove2.me/theorems/3b19bec6-fc02-41b1-99a0-6ae2dadd3851
-- title:
--   A Sobolev bound for the diagonal Hermite trace
-- statement:
--   Suppose the squared modulus of the zeroth coefficient is at most $u$ and every finite sum of $n^2|d_n|^2$ over positive modes is at most $v$. Then the diagonal series $\sum z^n d_n$ converges absolutely on the closed unit disk. Its squared modulus is at most $\tfrac32(u+4v)$.
-- source:
--   Saha et al., arXiv:2608.11158v2, Appendix C.2, the boundary trace estimate (51). The elementary telescoping bound for the reciprocal-square sum gives the factor 3/2 in this form.

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Group.InfiniteSum

namespace GrothendieckLB.Supplement



theorem diagonal_hermite_sobolev_bound (d : ℕ → ℂ) (z : ℂ) (hz : ‖z‖≤1) (u v : ℝ)
    (hu : ‖d 0‖^2≤u) (hv : ∀ n : ℕ, (∑ k ∈ Finset.range n, ((k:ℝ)+1)^2*‖d (k+1)‖^2)≤v) :
    Summable (fun n : ℕ => z^n*d n) ∧ ‖∑' n : ℕ, z^n*d n‖^2≤(3/2:ℝ)*(u+4*v) := by sorry

end GrothendieckLB.Supplement
