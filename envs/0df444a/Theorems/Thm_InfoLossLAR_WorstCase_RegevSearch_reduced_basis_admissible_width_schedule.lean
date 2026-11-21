-- Prove2me | Theorems.Thm_InfoLossLAR_WorstCase_RegevSearch_reduced_basis_admissible_width_schedule
-- name    : InfoLossLAR.WorstCase.RegevSearch.reduced_basis_admissible_width_schedule
-- status  : Proved
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-21T02:31:25.456271+00:00
-- url     : https://prove2.me/theorems/b2022bb4-12ce-4c27-92a0-d9a762dce103
-- title:
--   A dimension-bounded Gaussian width schedule for the input lattice
-- statement:
--   Let $n\ge2$, let $B$ be a nonsingular integer basis in dimension $n$, and let the positive rational $r$ satisfy the Gaussian sampling threshold for $B$. There exists another integer basis $D$ of the same lattice such that the rational initial width
--   $$W=\max\{(n+1)(1+\textstyle\sum_{i,j}|D_{ij}|),r\sigma_n\}$$
--   reaches a valid terminal width after at most $5n+2$ halvings. Every source width $W/2^j$ up to and including the terminal stage exceeds $\sqrt2\,q_n\eta_{\varepsilon_n}(B\mathbb Z^n)$. At the terminal stage $h$, the decoding radius $\sigma_n/(2W/2^h)$ is at least $\sqrt n/(\sqrt2r)$.
-- source:
--   Regev, On Lattices, Learning with Errors, Random Linear Codes, and Cryptography, Theorem 3.1 and Lemma 3.3, https://cims.nyu.edu/~regev/papers/qcrypto.pdf. The reduced-basis initialization floor and the $5n+2$ bound at arbitrary promised rational width are explicit specializations for https://prove2.me/theorems/9fdfd0c1-342f-4e71-9410-562b6727463a.

import Definitions.Def_InfoLossLAR_RegevSketch_DGS
set_option autoImplicit false
open scoped BigOperators
open RegevLWE.GaussConv
open InfoLossLAR.WorstCase InfoLossLAR.WorstCase.RegevSketch

namespace InfoLossLAR.WorstCase.RegevSearch

theorem reduced_basis_admissible_width_schedule {n : ℕ} (hn : 2 ≤ n)
    (B : Matrix (Fin n) (Fin n) ℤ) (hB : B.det ≠ 0)
    (r : ℚ) (hr : 0 < r) (hp : dgsThreshold B ≤ (r : ℝ)) :
    ∃ D : Matrix (Fin n) (Fin n) ℤ, D.det ≠ 0 ∧ inputModule D = inputModule B ∧
    ∃ W : ℚ, W = max (((n+1 : ℕ) : ℚ) * (1 + ∑ i, ∑ j, |(D i j : ℚ)|)) (r * (famσ n : ℚ)) ∧
    ∃ h : ℕ, h ≤ 5*n+2 ∧
      (∀ j ≤ h, Real.sqrt 2 * (famq n : ℝ) * smoothingParam (inputModule B) (smoothingError n) <
        (W : ℝ) / 2^j) ∧
      Real.sqrt n / (Real.sqrt 2 * (r : ℝ)) ≤ (famσ n : ℝ)/(2*((W : ℝ)/2^h)) := by
  sorry

end InfoLossLAR.WorstCase.RegevSearch
