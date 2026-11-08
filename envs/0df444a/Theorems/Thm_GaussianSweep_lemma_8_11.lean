-- Prove2me | Theorems.Thm_GaussianSweep_lemma_8_11
-- name    : GaussianSweep.lemma_8_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T07:53:59.444099+00:00
-- url     : https://prove2.me/theorems/24cf8ca3-fc10-4a04-8f43-5c4bc91fb269
-- title:
--   Lemma 8.11 — two exceedances: $\Pi_C(h) \ge \Pi_{C_{\mathrm{eq}}}(h)$
-- statement:
--   For every $3 \times 3$ correlation matrix $C$ (positive semidefinite with unit diagonal, singular matrices included) and every $h > 0$,
--   $$
--   \Pi_C(h) \ge \Pi_{C_{\mathrm{eq}}}(h),
--   $$
--   where $\Pi_C(h)$ is the probability that at least two coordinates of $\eta \sim N(0, C)$ exceed $h$ and $C_{\mathrm{eq}}$ is the equilateral correlation matrix (off-diagonal entries $-\tfrac12$). Among all correlation structures of three standard normals, the equilateral one minimizes the probability of two exceedances.
--
--   Differences from the source: none.
-- source:
--   Gaspers, Path Decompositions of Sparse Graphs via Gaussian Sweeps and Faster Exponential Algorithms, arXiv:2611.05146 (held version, sha256 e0ed039f…9eac), Lemma 8.11, p.52 (PDF p.54)

import Mathlib
import Definitions.Def_GaussianSweep_Ceq
import Definitions.Def_GaussianSweep_PiC

namespace GaussianSweep

/-- Lemma 8.11 (two exceedances) (Gaspers, *Path Decompositions of Sparse Graphs via Gaussian Sweeps and Faster Exponential Algorithms*, arXiv:2611.05146 (held version, sha256 e0ed039f…9eac), Lemma 8.11, p.52 (PDF p.54)). For every `3 × 3`
correlation matrix `C` and every `h > 0`, `Π_C(h) ≥ Π_{C_eq}(h)`.

**Formalization Note** A correlation matrix is a positive semidefinite matrix with unit diagonal
(Section 4.4, p.25), singular ones included. -/
theorem lemma_8_11 (C : Matrix (Fin 3) (Fin 3) ℝ) (hC : C.PosSemidef) (hdiag : ∀ i, C i i = 1)
    (h : ℝ) (hh : 0 < h) : PiC Ceq h ≤ PiC C h := by sorry

end GaussianSweep
