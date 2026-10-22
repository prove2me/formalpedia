-- Prove2me | Theorems.Thm_NisetNoGo_GECC_entanglement_breaking
-- name    : NisetNoGo.GECC.entanglement_breaking
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:32:08.244173+00:00
-- url     : https://prove2.me/theorems/a28fc870-f5c1-4c79-9dc3-c64b2ec8dfef
-- title:
--   p. 3 — nonpositive determinant channels are entanglement breaking
-- statement:
--   Let $T=(M,N)$ be a completely positive single-mode Gaussian channel with $\det M\le0$. For every finite squeezing parameter $r$, the smallest partially transposed symplectic eigenvalue of the state obtained by applying $T$ to one half of the two-mode squeezed vacuum satisfies
--
--   $$\nu_-(r)\ge1.$$
--
--   Consequently the output has zero logarithmic negativity. This covers the negative and zero determinant classes of channels.
--
--   **Formalization Note** The printed text calls $\nu_-$ “larger than one”; the non-strict inequality includes the product-state boundary where equality holds.
-- source:
--   Niset, Fiurášek, Cerf, A No-Go Theorem for Gaussian Quantum Error Correction, arXiv:0811.3128v1, p. 3, paragraph following (10)

import Mathlib
import Definitions.Def_NisetNoGo_GECC_Setup

open QAlgorithms.Papers.Independent.Frontier30.P13

namespace NisetNoGo.GECC

theorem entanglement_breaking
    (M N : Matrix (ModeQuadrature (Fin 1)) (ModeQuadrature (Fin 1)) ℝ)
    (hT : IsCPChannel M N) (hdet : M.det ≤ 0) :
    ∀ r : ℝ, 1 ≤ lambdaMin (gammaOut M N r) := by sorry

end NisetNoGo.GECC
