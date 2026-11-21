-- Prove2me | Theorems.Thm_InfoLossLAR_WorstCase_RegevSearch_native_reduced_basis_halving_window
-- name    : InfoLossLAR.WorstCase.RegevSearch.native_reduced_basis_halving_window
-- status  : Proved
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-21T05:22:47.575996+00:00
-- url     : https://prove2.me/theorems/b3909c5c-d3c7-4b85-b9f4-e67f48ea2c5e
-- title:
--   A halving window for the width initialized by the native LLL basis
-- statement:
--   Let $B$ be a nonsingular integer basis of dimension $n\ge 2$ and let $r>0$ be a rational width satisfying the discrete Gaussian sampling promise. Compute the native LLL basis $D$ of $B$. Let $W$ be the larger of $(n+1)(1+\sum_{i,j}|D_{ij}|)$ and $r\sigma_n$, and set $w=r\sigma_n/\sqrt{2n}$. The first integer $k$ for which $W/2^k\le w$ is at most $5n+2$, and its width lies in $[w/2,w]$.
-- source:
--   The actual native LLL initialization and first-crossing estimate in the proof of InfoLossLAR.WorstCase.RegevSearch.reduced_basis_admissible_width_schedule. This version specifies the computed basis and the position of the first crossing, both used by the coherent shared-pool Fourier sampler.

import Definitions.Def_InfoLossLAR_RegevSketch_DGS
import Definitions.Def_LARLLL_CurrentData

set_option autoImplicit false
open scoped BigOperators
open InfoLossLAR.WorstCase InfoLossLAR.WorstCase.RegevSketch

namespace InfoLossLAR.WorstCase.RegevSearch

theorem native_reduced_basis_halving_window {n : ℕ} (hn : 2 ≤ n) (B : Matrix (Fin n) (Fin n) ℤ)
    (hB : B.det ≠ 0) (r : ℚ) (hr : 0 < r) (hp : dgsThreshold B ≤ (r:ℝ)) :
    let D:=NativeLLL.basis B
    let W : ℝ:=(max (((n+1 : ℕ) : ℚ)*(1+∑ i,∑ j,|(D i j:ℚ)|)) (r*(famσ n:ℚ)) : ℚ)
    let w:=(r:ℝ)*(famσ n:ℝ)/(Real.sqrt 2*Real.sqrt n)
    ∃ k : ℕ, k ≤ 5*n+2 ∧ w/2 ≤ W/2^k ∧ W/2^k ≤ w ∧ ∀ j < k, w < W/2^j := by
  sorry

end InfoLossLAR.WorstCase.RegevSearch
