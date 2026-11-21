-- Prove2me | Theorems.Thm_InfoLossLAR_WorstCase_RegevSearch_residual_variance_grid_gaussian_tv
-- name    : InfoLossLAR.WorstCase.RegevSearch.residual_variance_grid_gaussian_tv
-- status  : Proved
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-21T02:25:43.200775+00:00
-- url     : https://prove2.me/theorems/44081977-ca1c-4b0d-89f7-5b3b2ea8f763
-- title:
--   One variance guess controls all residual integer Gaussian laws
-- statement:
--   Let $s,q\ge2$ and $M\ge1$ be integers. Let $E\in[0,s^2/2]$ be an unknown initial noise energy. Write $D_w(z)\propto\exp(-\pi z^2/w^2)$ for the normalized discrete Gaussian on $\mathbb Z$. There is a single index $0\le i\le M$ such that at every stage $j\ge0$ the publicly specified rational variance $v_j=s^2-(s^2/2)(i/M)q^{-2j}$ belongs to $[s^2/2,s^2]$. For $V_j=E q^{-2j}+v_j$ one has
--   $$0\le s^2-V_j\le\frac{s^2}{2Mq^{2j}},\qquad d_{\rm TV}(D_{\sqrt{V_j}},D_s)\le\frac{1}{Mq^{2j}}.$$
--   Under correct modular residual updates in bounded-distance decoding, the energy falls by $q^{-2}$ per digit. Consequently, all digits admit the same one of the $M+1$ publicly enumerable variance schedules.
-- source:
--   Specialization to the exact integer Gaussian in InfoLossLAR.WorstCase.RegevSearch.search_to_shared_pool_bdd (https://prove2.me/theorems/0bf36425-687f-493d-a04f-ac2e81e7e02e). Regev, On Lattices, Learning with Errors, Random Linear Codes, and Cryptography, §3.2.1, Lemma 3.5 (recursion) and Lemma 3.11 (noise), https://cims.nyu.edu/~regev/papers/qcrypto.pdf. The simultaneous rational grid and its sharp discrete bound are derived here. The scalar identity used is Mathlib Real.tsum_exp_neg_mul_int_sq (Gaussian Poisson summation).

import Definitions.Def_InfoLossLAR_NativeSparsePrefix_01
import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation

set_option autoImplicit false
open scoped BigOperators

namespace InfoLossLAR.WorstCase.RegevSearch

theorem residual_variance_grid_gaussian_tv
    (s q M : ℕ) (hs : 2 ≤ s) (hq : 2 ≤ q) (hM : 0 < M)
    (E : ℝ) (hE : 0 ≤ E) (hcap : E ≤ (s : ℝ)^2 / 2) :
    ∃ i : Fin (M + 1), ∀ j : ℕ,
      let den : ℚ := (q : ℚ)^(2*j)
      let v : ℚ := (s : ℚ)^2 - ((s : ℚ)^2/2) * (i.val : ℚ) / M / den
      let total := E / (den : ℝ) + (v : ℝ)
      let mass := fun (width : ℝ) (z : ℤ) => AFT.GaussianSource.weight width z /
        AFT.GaussianSource.realNormalizer width
      (s : ℚ)^2/2 ≤ v ∧ v ≤ (s : ℚ)^2 ∧
      0 ≤ (s : ℝ)^2 - total ∧
      (s : ℝ)^2 - total ≤ (s : ℝ)^2 / (2 * M * (den : ℝ)) ∧
      (∑' z : ℤ, |mass (Real.sqrt total) z - mass (s : ℝ) z|)/2 ≤
        1 / ((M : ℝ) * (den : ℝ)) := by
  sorry

end InfoLossLAR.WorstCase.RegevSearch
