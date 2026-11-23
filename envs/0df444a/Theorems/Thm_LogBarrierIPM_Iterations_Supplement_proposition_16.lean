-- Prove2me | Theorems.Thm_LogBarrierIPM_Iterations_Supplement_proposition_16
-- name    : LogBarrierIPM.Iterations.Supplement.proposition_16
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T17:22:11.841025+00:00
-- url     : https://prove2.me/theorems/2b43ad16-9110-4c84-a861-60c54f20dedd
-- title:
--   Proposition 16 — finite pieces and complementary derivatives
-- statement:
--   Under Assumption 13, the general tropical central path $C^{\rm trop}:\mathbb R\to\mathbb R^{2N}$ is monotone and continuous with finitely many affine pieces on the whole real line. At every point $\lambda$ where it is differentiable,
--   $$\frac{d}{d\lambda}C^{\rm trop}(\lambda)=(e^K,e^{[N]\setminus K})\quad\text{for some }K\subseteq[N].$$
--   The two halves are $(x,w)$ and $(s,y)$ in the same index order. Finite piecewise affine means that a finite set of breakpoints partitions every interval into affine pieces, including the two unbounded tails. These structural properties are used by both the uniform bound and the segment-count argument.
--
--   Differences from the source:
--   - encoding: the point C^trop(λ) of T^{2N}, indexed from 1 → a real vector indexed by Fin ((n+m)+(n+m)), in the order x, w, s, y; reason: under Assumption 13 all coordinates are finite by (20); Theorem 15 asserts that this vector is the barycenter
--   - encoding: monotone piecewise linear → a monotone continuous curve with a finite set of affine breakpoints and HasDerivAt at every smooth point; reason: this spells out the finite polygonal curve and the full paired derivative stated on p. 16
-- source:
--   Allamigeon, Benchimol, Gaubert, Joswig, Log-Barrier Interior Point Methods Are Not Strongly Polynomial, arXiv:1708.01544v2, p. 16, Proposition 16

import Mathlib
import Definitions.Def_LogBarrierIPM_Iterations_Supplement_TropicalLP

open Filter Matrix

namespace LogBarrierIPM.Iterations.Supplement
open LogBarrierIPM.Curvature

theorem proposition_16 {m n : ℕ} (A : Matrix (Fin m) (Fin n) Puiseux)
    (b : Fin m → Puiseux) (c : Fin n → Puiseux)
    (hstrict : StrictlyFeasibleK A b c) :
    Monotone (tropicalPath A b c) ∧ FinitePiecewiseAffine (tropicalPath A b c) ∧
    ∀ lam : ℝ, DifferentiableAt ℝ (tropicalPath A b c) lam →
      ∃ K : Set (Fin (n + m)),
        HasDerivAt (tropicalPath A b c) (pairedDirection K) lam := by sorry

end LogBarrierIPM.Iterations.Supplement
