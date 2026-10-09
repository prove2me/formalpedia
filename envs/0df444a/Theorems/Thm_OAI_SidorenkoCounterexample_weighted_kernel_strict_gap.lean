-- Prove2me | Theorems.Thm_OAI_SidorenkoCounterexample_weighted_kernel_strict_gap
-- name    : OAI.SidorenkoCounterexample.weighted_kernel_strict_gap
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-10-08T15:16:16.915557+00:00
-- url     : https://prove2.me/theorems/b4c76659-9dd1-40f3-b38f-32acd0418b33
-- title:
--   A symmetric finite kernel with a strict Sidorenko gap
-- statement:
--   For the fixed 35-vertex, 66-edge incidence pattern $H$, there exists a finite probability space with a symmetric kernel $W$ taking values in $[0,1]$, whose edge mean $\mu$ and pattern moment $\tau$ satisfy
--
--   $$
--   0<\mu,\qquad \tau<\mu^{66}.
--   $$
--
--   The edge mean averages $W$ over two independent states, and the pattern moment averages the product of $W$ over all incidence edges, with an independent state at every pattern vertex. This is the weighted-kernel stage of the finite counterexample; the host graph is obtained in a separate sampling stage.
--
--   **Formalization Note** The finite state space is represented by $\mathrm{Fin}(k)$ and its probability law by an explicit nonnegative vector of total mass one.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Sidorenko/Symmetrization.lean#L137, lemma exists_symmetric_kernel; also Types.lean, kernelMean and bipartiteMoment. Reindexed finite-state version of that lemma.

import Mathlib
import Definitions.Def_SidorenkoWeightedKernelData

theorem OAI.SidorenkoCounterexample.weighted_kernel_strict_gap :
    ∃ K : OAI.SidorenkoCounterexample.WeightedKernelData,
      0 < OAI.SidorenkoCounterexample.kernelEdgeMean K ∧
      OAI.SidorenkoCounterexample.kernelPatternMoment K <
        (OAI.SidorenkoCounterexample.kernelEdgeMean K) ^ 66 := by sorry
