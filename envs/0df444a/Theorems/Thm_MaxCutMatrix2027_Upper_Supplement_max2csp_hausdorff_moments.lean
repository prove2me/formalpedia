-- Prove2me | Theorems.Thm_MaxCutMatrix2027_Upper_Supplement_max2csp_hausdorff_moments
-- name    : MaxCutMatrix2027.Upper.Supplement.max2csp_hausdorff_moments
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:14:04.748031+00:00
-- url     : https://prove2.me/theorems/a5ac9a99-57cc-45ce-8bca-65cccb8ae2e8
-- title:
--   Lemma A.4 — MAX-2CSP Hausdorff moments
-- statement:
--   Let $y_{i,a}$ ($i\in[n]$, $a\in\{0,1\}$) be arbitrary vectors in a finite-dimensional real Euclidean space and let $1\le s\le n$ be real. Include each variable $i$ independently with probability $s/n$ (one selector $\xi_i$ per variable, shared by both labels). With
--   $$K=\Bigl\{\frac1n\sum_{i,a}z_{i,a}y_{i,a}:z\in\mathcal X\Bigr\},\quad K_Q=\Bigl\{\frac1s\sum_{i,a}\xi_iz_{i,a}y_{i,a}:z\in\mathcal X\Bigr\},\quad \Delta=d_H(K_Q,K),\quad t_y=\frac1n\sum_{i,a}\|y_{i,a}\|^2,$$
--   we have
--   $$\mathbb E[\Delta]\le4\sqrt{t_y/s},\qquad \mathbb E[\Delta^2]\le\frac{17\,t_y}{s}.$$
--
--   The retained spectral vectors $y_{i,a}=(\lambda_j\phi_j(i,a))_j$ of p.44, including zero retained rank, are a particular choice. These moments control the sampling error of the retained part.
--
--   Differences from the source:
--   - encoding: vertices (variables) labelled by [n] → Fin n = {0,…,n−1}; reason: relabeling is bijective
--   - encoding: independent Bernoulli(s/n) selectors → the exact finite Bernoulli-subset expectation sampleAverage (s/n); reason: the subset weights are exactly the independent-selector law
--   - generalization: the retained spectral vectors y_{i,a} of p.44 → arbitrary vectors y_{i,a} in any finite-dimensional real Euclidean space; reason: the proof on pp.45–47 uses only the support functions max_a⟨v, y_{i,a}⟩ and the squared lengths; the spectral vectors are one instance
--   - encoding: d_H between the nonempty compact convex sets K_Q, K → Metric.hausdorffDist in EuclideanSpace; reason: both sets are nonempty compact images of the compact set X, where Mathlib's value is the usual Hausdorff distance
-- source:
--   Songhua He, STOC 2027 submission #351 (October 2026), Lemma A.4, p.45 (PDF p.45); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/351.pdf; PDF SHA-256 b38cd84079663d9e2eb7375d7bf1572d5dc7c2157cfaf90e175fd371a9503631

import Definitions.Def_MaxCutMatrix2027_Upper_Supplement_CSP
import Definitions.Def_MaxCutMatrix2027_Upper_MatrixModel
set_option autoImplicit false

namespace MaxCutMatrix2027.Upper.Supplement

/-- Lemma A.4, p.45, stated for arbitrary Euclidean vectors `y_{i,a}` (the retained spectral
vectors of p.44 are one instance, including zero retained rank). -/
theorem max2csp_hausdorff_moments (n d : ℕ) (y : Fin n × Bool → EuclideanSpace ℝ (Fin d))
    (s : ℝ) (hs : 1 ≤ s) (hsn : s ≤ n) :
    sampleAverage (s / n) (cspSampleDistance y s) ≤ 4 * Real.sqrt (cspEnergy y / s) ∧
    sampleAverage (s / n) (fun Q => cspSampleDistance y s Q ^ 2) ≤ 17 * cspEnergy y / s := by sorry

end MaxCutMatrix2027.Upper.Supplement
