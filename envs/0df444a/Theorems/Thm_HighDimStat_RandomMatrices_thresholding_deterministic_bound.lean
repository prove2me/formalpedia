-- Prove2me | Theorems.Thm_HighDimStat_RandomMatrices_thresholding_deterministic_bound
-- name    : HighDimStat.RandomMatrices.thresholding_deterministic_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-20T04:23:16.69196+00:00
-- url     : https://prove2.me/theorems/192c29ef-9363-4335-aab6-541e01579575
-- title:
--   Eq. (6.54) -- the deterministic thresholding bound
-- statement:
--   **Eq. (6.54)** (the deterministic result underlying Theorem 6.23's proof). For any choice of
--   $\lambda_n$ such that $\|\hat\Sigma-\Sigma\|_{\max}\le\lambda_n$, we are guaranteed that
--
--   $$
--   |\!|\!|T_{\lambda_n}(\hat\Sigma)-\Sigma|\!|\!|_2 \;\le\; 2|\!|\!|A|\!|\!|_2\lambda_n,
--   $$
--
--   where $A$ is the adjacency matrix of $\Sigma$'s sparsity pattern. This purely deterministic
--   fact — no randomness or probability appears — reduces Theorem 6.23's proof to checking that
--   the max-norm deviation $\|\hat\Sigma-\Sigma\|_{\max}$ is controlled with high probability.
--
--   **Formalization Note** This is an unnumbered equation in the book, cited as `Eq. (6.54)` per
--   `BRIEF.md`'s own guidance, not invented as a milestone.
-- source:
--   Wainwright, High-Dimensional Statistics, CUP 2019, p. 181 (PDF p. 201), Eq. (6.54)

import Mathlib
import Definitions.Def_HighDimStat_RandomMatrices_thresholdMatrix
import Definitions.Def_HighDimStat_RandomMatrices_adjacencyMatrix
import Definitions.Def_HighDimStat_RandomMatrices_maxNorm
import Definitions.Def_HighDimStat_RandomMatrices_opNorm

namespace HighDimStat.RandomMatrices

/-- **Eq. (6.54)** (deterministic thresholding bound), Wainwright, *High-Dimensional Statistics*
(2019), p. 181. For any `λn` such that `‖Σ̂-Σ‖_max ≤ λn`, the thresholded matrix satisfies
`|||Tλn(Σ̂)-Σ|||₂ ≤ 2|||A|||₂λn`, where `A` is the adjacency matrix of `Σ`'s sparsity pattern. -/
theorem thresholding_deterministic_bound {d : ℕ} (SigHat Sig : Matrix (Fin d) (Fin d) ℝ)
    (lam : ℝ) (hmax : maxNorm (SigHat - Sig) ≤ lam) :
    opNorm (thresholdMatrix lam SigHat - Sig) ≤ 2 * opNorm (adjacencyMatrix Sig) * lam := by sorry

end HighDimStat.RandomMatrices
