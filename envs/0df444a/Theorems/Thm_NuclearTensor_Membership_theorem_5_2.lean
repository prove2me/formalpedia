-- Prove2me | Theorems.Thm_NuclearTensor_Membership_theorem_5_2
-- name    : NuclearTensor.Membership.theorem_5_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T22:18:39.913679+00:00
-- url     : https://prove2.me/theorems/529785a9-98c5-4b7b-b8b7-898937802e12
-- title:
--   Theorem 5.2 — weak membership in a convex product hull
-- statement:
--   Under exactly the convex local-set and approximate linear-oracle assumptions of Lemma 5.1, let $C=\operatorname{conv}\{x_1\otimes\cdots\otimes x_k:x_j\in K_j\}$. For every $\epsilon>0$, a deterministic program on every explicit real tensor $M$ accepts $M\in C$ and rejects $\operatorname{dist}_F(M,C)\ge\epsilon$, including equality, within
--   $$B_\epsilon\,d^{C_\epsilon k}.$$
--   The positive constants are chosen before the dimensions, local sets, services, and input. No input-norm or near/far promise is a hypothesis, and the program terminates within its bound on gap inputs as well.
--
--   The source norm-rejection branch is explicit. For the remaining branch, put $\epsilon_0=\min(\epsilon,1)$, use $T=\lceil128/\epsilon_0^2\rceil+1$ Frank–Wolfe steps, normalize each direction by its actual norm capped below at one, use normalized product accuracy $\epsilon_0^2/[16(3+\epsilon)]$, and compare $F(Y_T)=\|Y_T-M\|_F^2/2$ with $\epsilon^2/4$. These choices give objective error at most $\epsilon_0^2/8$, below the far optimum $\epsilon^2/2$. The direction routine is finite existentially constructed code, not a free global oracle. This target includes the full weak-membership conclusion on the original convex hull, without closing the local feasible sets.
--
--   Differences from the source:
--
--   - encoding: finite-dimensional real Hilbert spaces, indexed from 1 → zero-based row-major Euclidean coordinates, allowing zero-dimensional local spaces; reason: orthonormal coordinates represent every source finite real Hilbert space; positive tensor order is the source convention
--   - reading: polynomial time on arbitrary real inputs with polynomial-time SVD and stipulated local linear optimizers → finite offline real-RAM programs with scalar arithmetic, square root, charged full SVD, explicit finite-code calls, and only the stipulated local services; reason: the source specifies no bit lengths; fixed positive model parameters A and q charge spectral and local operations, while actual executions determine every total runtime
--   - reading: maxima over convex local sets not assumed compact in Lemma 5.1 → suprema over exactly the original feasible sets, with actual returned points in those sets; reason: the open unit disk has arbitrary-accuracy local linear optimization but no maximizer for v=(1,0); this retains the nonclosed cases instead of adding compactness
--   - encoding: the real infimum defining Frobenius distance to the convex product hull → a complete-lattice nonnegative extended-real distance infimum; reason: the original feasible hull is nonempty and distances are bounded below by zero; no empty real-infimum default is used
--   - encoding: O(epsilon^2) errors and a separated near/far decision in the source Frank–Wolfe proof → T=ceil(128/epsilon0^2)+1, normalized oracle accuracy epsilon0^2/(16(3+epsilon)), threshold epsilon^2/4; reason: fixed source-order parameters give objective error at most epsilon0^2/8; the actual gradient norm is accounted for and every external positive accuracy is covered
-- source:
--   Martino Bernasconi, Giulio Malavolta, STOC 2027 submission #945 (October 2026), p.20, Theorem 5.2 and whole proof

import Definitions.Def_NuclearTensor_Membership_Optimization

set_option autoImplicit false
noncomputable section
open scoped BigOperators ENNReal

namespace NuclearTensor.Membership

theorem theorem_5_2 :
    ∀ ε : ℝ, 0 < ε → ∃ P Pdir : Program,
      ∀ (σ : Spectral) (A q : ℕ), 0 < A → 0 < q →
      ∃ B C : ℕ, 0 < B ∧ 0 < C ∧
      ∀ O : LocalOracle, O.dimensions ≠ [] → 2 ≤ maxDimension O.dimensions →
      ∀ K : (j : ℕ) → Set (Vec (O.dimensions.getD j 0)),
        sourceSets O.dimensions K → localOracleContract O K →
        ∀ M : Tensor O.dimensions,
          runsWithin σ (some O) A q [Pdir] P (O.dimensions.map Int.ofNat) ([ε] ++ encodeVec M)
            (B * (maxDimension O.dimensions) ^ (C * O.dimensions.length))
            (fun s => ∃ b : Bool, outputsDecision s b ∧
              weakMembership (productHull K) ε M b ∧
              frankWolfeBehavior σ A q O Pdir ε M b) := by sorry

end NuclearTensor.Membership
