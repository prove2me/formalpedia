-- Prove2me | Theorems.Thm_LimitedBFGS_SQN_pcg_joint_prefix_invariants
-- name    : LimitedBFGS.SQN.pcg_joint_prefix_invariants
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-28T11:20:47.976342+00:00
-- url     : https://prove2.me/theorems/b8b0ad8d-c614-4cfd-b21c-3574eaf9c6c2
-- title:
--   Eq. (16), p. 777 — simultaneous forward induction: the three one-sided prefix invariants D, G, C of the PCG iteration with fixed H0
-- statement:
--   Along the preconditioned conjugate gradient iteration (13) of Nocedal 1980, p. 777, with the fixed symmetric positive definite preconditioner H0 and exact line searches, write g_k = grad A b (pcgIter A b H0 x0 k).x and d_k = (pcgIter A b H0 x0 k).d. For every k all three of the following hold simultaneously:
--
--   * D(k): g_k^T d_j = 0 for all j < k;
--   * G(k): g_k^T (H0 *v g_j) = 0 for all j < k;
--   * C(k): d_k^T (A *v d_j) = 0 for all j < k.
--
--   Why the simultaneous induction is well founded. The step from k to k+1 consumes its premises in the fixed order
--
--       old C, old D, old G  ->  new D  ->  new G  ->  new C,
--
--   so no invariant is ever established in isolation from itself, and no step needs a hypothesis that is only produced later in the same step. The earlier attempt to obtain the H0-pairing at (p, q) on its own is circular: reading the direction recurrence H0 *v g_j = -d_j + beta_j d_{j-1} shows it requires g_p^T d_j = 0 for j < p, which is itself an open target. This theorem is the joint system that breaks the circularity, and it is strictly stronger than any one of its three conjuncts.
--
--   Successor D. At j = k the exact line search gives g_{k+1} . d_k = 0 outright. At j < k, the affine-gradient identity g_{k+1} - g_k = a_k (A *v d_k) gives g_{k+1} . d_j = g_k . d_j + a_k d_k . (A *v d_j), which vanishes by old D and old C.
--
--   Successor G. At j = 0, the identity d_0 = -(H0 *v g_0) turns new D at column 0 into -(g_{k+1} . (H0 *v g_0)) = 0. At 0 < j, the direction recursion g_{k+1} . d_j = -(g_{k+1} . (H0 *v g_j)) + beta_j (g_{k+1} . d_{j-1}) has both dot products among the columns of NEW D, so the beta term vanishes with no hypothesis on beta at all: its possibly-zero denominator y_j . d_j is never touched and beta is never unfolded.
--
--   Successor C. At j = k this is the one-step A-conjugacy. At j < k, expanding only the direction recurrence d_{k+1} = -(H0 *v g_{k+1}) + beta_k d_k, the beta_k d_k term dies by old C, and what remains is T := (H0 *v g_{k+1}) . (A *v d_j). Using g_{j+1} - g_j = a_j (A *v d_j) and symmetry of H0, a_j * T = g_{k+1} . (H0 *v g_{j+1}) - g_{k+1} . (H0 *v g_j) = 0 by new G at j+1 and at j. When a_j is nonzero we cancel a_j. When a_j vanishes that identity degenerates to g_{j+1} = g_j, so the two new-G columns are the same equation and T is unconstrained; that branch is closed by exactStep_zero_gives_zero_dir, which gives d_j = 0 and hence A *v d_j = 0. This is the only input from outside the three invariants.
--
--   No step uses termination, the step-coefficient formula, or any global orthogonality or conjugacy statement. Consequences: one-sided G plus symmetry of H0 gives the pairwise gradient orthogonality g_i^T H0 g_j = 0 for i != j; one-sided D gives the second half of the gradient/direction orthogonality; one-sided C plus symmetry of A gives global A-conjugacy of the directions, and hence d_i^T y_j = 0 for i != j with no division at all.
-- source:
--   Nocedal, J. (1980), 'Updating Quasi-Newton Matrices with Limited Storage', Mathematics of Computation 35(151), 373-382, eq. (15)-(16) and iteration (13) at p. 777.

import Mathlib
import Definitions.Def_LimitedBFGS_SQN_pcgIter

open Matrix

namespace LimitedBFGS.SQN
theorem pcg_joint_prefix_invariants {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (b : Fin n → ℝ) (H₀ : Matrix (Fin n) (Fin n) ℝ) (hH₀ : H₀.PosDef) (x₀ : Fin n → ℝ) :
    ∀ k : ℕ,
      (∀ j < k, grad A b (pcgIter A b H₀ x₀ k).x ⬝ᵥ (pcgIter A b H₀ x₀ j).d = 0) ∧
      (∀ j < k, grad A b (pcgIter A b H₀ x₀ k).x ⬝ᵥ
        (H₀ *ᵥ grad A b (pcgIter A b H₀ x₀ j).x) = 0) ∧
      (∀ j < k, (pcgIter A b H₀ x₀ k).d ⬝ᵥ (A *ᵥ (pcgIter A b H₀ x₀ j).d) = 0) := by sorry
end LimitedBFGS.SQN
