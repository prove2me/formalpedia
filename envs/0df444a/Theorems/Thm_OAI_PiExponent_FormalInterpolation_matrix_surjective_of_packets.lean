-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_matrix_surjective_of_packets
-- name    : OAI.PiExponent.FormalInterpolation.matrix_surjective_of_packets
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-07T19:41:15.394894+00:00
-- url     : https://prove2.me/theorems/4b414961-3af3-45a7-b5fa-d217d37922d3
-- title:
--   Transfer formal logarithmic packets to the actual truncated matrix
-- statement:
--   Let $d$ be an admissible determinant family and $H\in\mathbb Q$. Put $w_i=\lceil\log q_i\rceil$ and $T_i=\lceil F_0 w_i/v_0\rceil$. Assume that each truncation threshold dominates the corresponding jet weight:
--
--   $$\frac{w_i}{\theta}\le T_i v_0\qquad(1\le i\le m).$$
--
--   If weighted polynomials of column weight at most $H$ interpolate every coefficient packet of the formal logarithmic jets at the centers $j r$, then the actual matrix with logarithms truncated at the fixed orders $T_i$ is surjective:
--
--   $$J_d(H)\text{ surjective}\quad\Longrightarrow\quad M_d(H):\mathbb C^{\operatorname{Columns}_d(H)}\longrightarrow\mathbb C^{\operatorname{Rows}_d(H)}\text{ surjective}.$$
--
--   This isolates the passage between the formal jet model and the concrete finite matrix. The weight threshold is stated explicitly; no equality between infinite and truncated logarithmic coefficients is asserted.
--
--   **Formalization Note.** This specializes the source's truncatedLogMatrix_surjective_of_formalLog_packets to the actual admissible family. Polynomial degree is recorded in the domain subtype, and concrete row indices replace the equivalent rational coefficient packet indices.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/FormalMatrixSurjectivity.lean#L57-L83; Approximation/AdmissibleMatrixInterpolation.lean#L94-L115.

import Definitions.Def_OAI_PiExponent_FormalInterpolationPackets

open Filter Topology
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction

theorem OAI.PiExponent.FormalInterpolation.matrix_surjective_of_packets
    {nu : ℝ} (d : FixedData nu) (H : ℚ)
    (hT : ∀ i : Fin d.m,
      MatrixArithmetic.logWeights (finiteDenominators d) i / (d.base.theta : ℝ) ≤
        (MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0 i : ℝ) *
          (d.v0 : ℝ))
    (hpacket : Function.Surjective (FormalInterpolation.packetMap d (H : ℝ))) :
    Function.Surjective (actualMatrix d (H : ℝ)).mulVecLin := by sorry
