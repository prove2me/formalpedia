-- Prove2me | Theorems.Thm_NuclearTensor_Membership_lemma_5_1
-- name    : NuclearTensor.Membership.lemma_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T22:19:04.961352+00:00
-- url     : https://prove2.me/theorems/7353097a-4252-4bb3-b2c3-ae637784c8ef
-- title:
--   Lemma 5.1 — product optimization from local linear oracles
-- statement:
--   Let the local real Hilbert spaces have maximum dimension $d\ge2$, and let each $K_j$ be convex and contained in its local unit ball. Assume the stipulated polynomial-time approximate linear optimizer returns an actual feasible point for every objective and positive tolerance. Given $\|M\|_F\le1$ and any $\epsilon>0$, a deterministic finite program returns $x_j\in K_j$ with
--   $$\langle M,x_1\otimes\cdots\otimes x_k\rangle\ge\sup_{y_j\in K_j}\langle M,y_1\otimes\cdots\otimes y_k\rangle-\epsilon,$$
--   in time $d^{O_\epsilon(k)}$, as established in the source proof. The runtime constants precede all dimensions, feasible sets, local services, and input tensors once the fixed local/spectral cost convention is selected.
--
--   Both regimes are included: direct convex-projection covers for $k\le d^2$ and local feasible nets with balanced block regrouping for $k>d^2$. Projection accuracy is $\delta/8$ on a $\delta/4$ grid, with strict acceptance below $\delta/2$. Source parameters and actual witnesses are explicit program outputs. The budgets are at most $3\epsilon_0/4$ in either regime, with $\epsilon_0=\min(\epsilon,1)$, so the full requested error is retained. Compactness is not added to the original local sets; finite regrouped block options are compact independently. This is the general product optimizer used by weak membership.
--
--   Differences from the source:
--
--   - encoding: finite-dimensional real Hilbert spaces, indexed from 1 → zero-based row-major Euclidean coordinates, allowing zero-dimensional local spaces; reason: orthonormal coordinates represent every source finite real Hilbert space; positive tensor order is the source convention
--   - reading: polynomial time on arbitrary real inputs with polynomial-time SVD and stipulated local linear optimizers → finite offline real-RAM programs with scalar arithmetic, square root, charged full SVD, explicit finite-code calls, and only the stipulated local services; reason: the source specifies no bit lengths; fixed positive model parameters A and q charge spectral and local operations, while actual executions determine every total runtime
--   - reading: maxima over convex local sets not assumed compact in Lemma 5.1 → suprema over exactly the original feasible sets, with actual returned points in those sets; reason: the open unit disk has arbitrary-accuracy local linear optimization but no maximizer for v=(1,0); this retains the nonclosed cases instead of adding compactness
--   - encoding: Theta(epsilon/sqrt(m)) compression, Theta(epsilon/m) covers, and O(epsilon) terminal/net errors and Theta(sqrt(dk)) regrouping for k>d^2 → epsilon0=min(epsilon,1), eta=epsilon0/(8 sqrt(m)), delta=epsilon0/(4m), terminal tolerance=epsilon0/4, gamma=epsilon0/(4k); m=k for k<=d^2 and otherwise min(k,ceil sqrt(dk)) with balanced consecutive floor endpoints; reason: the p.17 bound is m delta+2 eta sqrt(m); terminal and discretization budgets retain the full epsilon conclusion, including both order/dimension regimes
--   - encoding: the constructions and witnesses in the proof of Lemma 5.1 → the same finite grids, tested projection prefixes, local nets, grouped covers, and terminal choices are materialized as additional program outputs; reason: ties both source regimes and witness storage to charged execution rather than postulating a global optimizer or a cost certificate
-- source:
--   Martino Bernasconi, Giulio Malavolta, STOC 2027 submission #945 (October 2026), pp.17–20, Lemma 5.1, both regimes and runtime proof

import Definitions.Def_NuclearTensor_Membership_Regimes

set_option autoImplicit false
noncomputable section
open scoped BigOperators ENNReal

namespace NuclearTensor.Membership

theorem lemma_5_1 :
    ∃ P : Program, ∀ (σ : Spectral) (A q : ℕ), 0 < A → 0 < q →
      ∀ ε : ℝ, 0 < ε → ∃ B C : ℕ, 0 < B ∧ 0 < C ∧
      ∀ O : LocalOracle, O.dimensions ≠ [] → 2 ≤ maxDimension O.dimensions →
      ∀ K : (j : ℕ) → Set (Vec (O.dimensions.getD j 0)),
        sourceSets O.dimensions K → localOracleContract O K →
        ∀ M : Tensor O.dimensions, ‖M‖ ≤ 1 →
          runsWithin σ (some O) A q [] P (O.dimensions.map Int.ofNat) ([ε] ++ encodeVec M)
            (B * (maxDimension O.dimensions) ^ (C * O.dimensions.length))
            (fun s => ∃ x : Tuple O.dimensions, outputsTuple s x ∧ x ∈ feasible K ∧
              inner ℝ M (product x) ≥ optimum M K - ε ∧
              realizesRegimes σ O K ε M s x) := by sorry

end NuclearTensor.Membership
