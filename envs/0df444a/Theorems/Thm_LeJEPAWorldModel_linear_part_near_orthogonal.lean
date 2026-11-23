-- Prove2me | Theorems.Thm_LeJEPAWorldModel_linear_part_near_orthogonal
-- name    : LeJEPAWorldModel.linear_part_near_orthogonal
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T17:22:15.265922+00:00
-- url     : https://prove2.me/theorems/3f46b294-c996-4173-a7de-45035b84d829
-- title:
--   Equation (48): approximate whitening forces the linear part near an orthogonal matrix
-- statement:
--   Let $z\sim\mathcal N(0,I_N)$, and let $h:\mathbb R^N\to\mathbb R^N$ be measurable with square-integrable coordinates and $\mathbb E[h(z)]=0$. Let $M_{ij}=\mathbb E[h_i(z)z_j]$ be its linear part and $W_{\mathrm{nl}}=\mathbb E\|h(z)-Mz\|^2$ its nonlinear energy. If $\|\mathrm{Cov}(h(z))-I_N\|_F\le\varepsilon$, then there is an orthogonal $Q\in O(N)$ with
--
--   $$\|M-Q\|_F\le\varepsilon+W_{\mathrm{nl}}.$$
--
--   Approximate whitening thus forces the linear part of the encoder to lie near an orthogonal matrix. In the paper, $Q$ is the orthogonal factor of the polar decomposition of $M$.
--
--   **Formalization Note** Square-integrability of $h(z)$ is implicit in the paper. Here it is an explicit hypothesis.
-- source:
--   Klindt, LeCun and Balestriero, When Does LeJEPA Learn a World Model?, arXiv:2605.26379v2 (2026), Appendix C.2, eqs. (46)-(48), p. 25

import Mathlib
import Definitions.Def_LeJEPAWorldModel_Basic

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace LeJEPAWorldModel

theorem linear_part_near_orthogonal (N : ℕ) (ε : ℝ)
    (h : (Fin N → ℝ) → Fin N → ℝ) (hmeas : Measurable h)
    (hL2 : ∀ i, MemLp (fun z => h z i) 2 (stdGaussian N))
    (hmean : ∀ i, ∫ z, h z i ∂stdGaussian N = 0)
    (hwhite : frobNorm (covMat N h - 1) ≤ ε) :
    ∃ Q ∈ Matrix.orthogonalGroup (Fin N) ℝ,
      frobNorm (linearPart N h - Q) ≤ ε + nonlinearEnergy N h := by sorry

end LeJEPAWorldModel
