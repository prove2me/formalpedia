-- Prove2me | Theorems.Thm_MixedCloning_Optimal_averageOverlap_le_transposedIntegrals
-- name    : MixedCloning.Optimal.averageOverlap_le_transposedIntegrals
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T03:46:16.749071+00:00
-- url     : https://prove2.me/theorems/3f9faf61-72e5-467a-adeb-6251f8cc0933
-- title:
--   Lemma 14 Schur step — Haar-average overlap bounded by transposed integrals
-- statement:
--   For a permutation-invariant channel $C$ and arbitrary orthonormal Schur-module bases $b_\lambda$, the Haar-average overlap is bounded by
--   \[
--   \sum_{\lambda\vdash n,\;\ell(\lambda)\le r}
--    \frac{\dim P_\lambda\,s_\lambda(1^d)}{r^n}
--    \max_{\mu\vdash m,\;\ell(\mu)\le r}
--    \left\|\int q_\lambda(\Pi_U)^T\otimes q_\mu(\Pi_U)\,dU\right\|_\infty .
--   \]
--   The finite maximum is encoded as the supremum of the image of `partitions m r`. This statement isolates the Choi--Schur expansion, the partial transpose, and the operator-norm estimate in Lemma 14, after the minimizing rotated projector has been selected.
-- source:
--   Paper #243, Lemma 14 and its proof, page 18: average the rotated-projector overlap, expand in the Schur basis using permutation invariance, and estimate the resulting Choi expression by the operator norms of the partially transposed Schur integrals.

import Definitions.Def_MixedCloning_Optimal_Schur

noncomputable section
open Matrix MeasureTheory
open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.Elementwise

namespace MixedCloning.Optimal
attribute [local instance] Classical.propDecidable Classical.decEq

theorem averageOverlap_le_transposedIntegrals (d r n m : ℕ) (hr : 1 ≤ r) (hrd : r ≤ d)
    (C : Cloner d n m) (hC : QAlgorithms.IsChannel C) (hperm : PermInvariant d n m C)
    (b : (L : YoungDiagram) → SchurBasis L d) :
    averageOverlap d r n m C ≤
      ∑ L ∈ partitions n r, (spechtDim L : ℝ) * schurCount L d / (r : ℝ)^n *
        sSup ((partitions m r).image fun M => operatorNorm (transposedIntegral r L M (b L) (b M))) := by sorry
