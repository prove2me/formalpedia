-- Prove2me | Theorems.Thm_NuclearTensor_Membership_theorem_3_1
-- name    : NuclearTensor.Membership.theorem_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T22:18:14.336798+00:00
-- url     : https://prove2.me/theorems/860dfab8-343b-4a37-89b4-68edf816a745
-- title:
--   Theorem 3.1 — uniform product-test compression
-- statement:
--   Given real finite-dimensional spaces $H_1,\ldots,H_k$, a tensor $M$ of Frobenius norm at most one, and $\eta>0$, a deterministic polynomial-time program returns the Algorithm 1 embeddings and terminal tensor, with $\dim V_j\le\eta^{-2}$. For every tuple of local unit-ball vectors, form the prefix messages $p_0=1$, $p_j=U_j^\dagger(p_{j-1}\otimes x_j)$. Then
--   $$\left|\langle M,x_1\otimes\cdots\otimes x_k\rangle-\langle\widetilde M,p_{k-1}\otimes x_k\rangle\right|\le\eta\sqrt{k}.$$
--   The same computed compression works for every product test. Its polynomial bound concerns actual execution, and its constants precede every shape, tensor, and threshold. This preserves both the source construction claim and its exact error constant.
--
--   Differences from the source:
--
--   - encoding: finite-dimensional real Hilbert spaces, indexed from 1 → zero-based row-major Euclidean coordinates, allowing zero-dimensional local spaces; reason: orthonormal coordinates represent every source finite real Hilbert space; positive tensor order is the source convention
--   - reading: polynomial time on arbitrary real inputs with polynomial-time SVD and stipulated local linear optimizers → finite offline real-RAM programs with scalar arithmetic, square root, charged full SVD, explicit finite-code calls, and only the stipulated local services; reason: the source specifies no bit lengths; fixed positive model parameters A and q charge spectral and local operations, while actual executions determine every total runtime
-- source:
--   Martino Bernasconi, Giulio Malavolta, STOC 2027 submission #945 (October 2026), p.9, Theorem 3.1; pp.12–14, Algorithm 1 and proof

import Definitions.Def_NuclearTensor_Membership_Optimization

set_option autoImplicit false
noncomputable section
open scoped BigOperators ENNReal

namespace NuclearTensor.Membership

theorem theorem_3_1 :
    ∃ P : Program, ∀ (σ : Spectral) (A q : ℕ), 0 < A → 0 < q →
      ∃ B p : ℕ, 0 < B ∧ 0 < p ∧
      ∀ (ds : List ℕ), ds ≠ [] → ∀ (M : Tensor ds), ‖M‖ ≤ 1 →
      ∀ η : ℝ, 0 < η →
        runsWithin σ none A q [] P (ds.map Int.ofNat) ([η] ++ encodeVec M)
          (B * inputSize ds ^ p)
          (fun s => ∃ C : PrefixData ds, outputsPrefix s C ∧ algorithm1 σ η M C ∧
            (∀ j, j + 1 < ds.length → (C.rank (j + 1) : ℝ) ≤ η ^ (-2 : ℤ)) ∧
            ∀ x : Tuple ds, (∀ j < ds.length, ‖x j‖ ≤ 1) →
              productTestError M C x ≤ η * Real.sqrt ds.length) := by sorry

end NuclearTensor.Membership
