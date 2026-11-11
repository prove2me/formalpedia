-- Prove2me | Theorems.Thm_HermiteLaptop_MaxAgree_theorem_4_5
-- name    : HermiteLaptop.MaxAgree.theorem_4_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T18:16:21.876306+00:00
-- url     : https://prove2.me/theorems/bf586f4c-8c1e-4abd-8fdf-cadb7463752f
-- title:
--   Theorem 4.5 — Algorithm 2 (better of 4-spokes and 5-spokes on an optimal SDP(0) solution) is a 0.7818-approximation for weighted MaxAgree
-- statement:
--   **MaxAgree.** Given a weighted edge-labelled simple graph on $V=\{1,\dots,n\}$ ($E_+\cap E_-=\emptyset$, $w_{ij}>0$), find a clustering $\mathcal C$ of $V$ maximizing
--   $$\mathrm{val}(\mathcal C)=\sum_{\{i,j\}\in E_+}w_{ij}\mathbf 1[\mathcal C(i)=\mathcal C(j)]+\sum_{\{i,j\}\in E_-}w_{ij}\mathbf 1[\mathcal C(i)\ne\mathcal C(j)],$$
--   with no limit on the number of clusters; $\mathrm{OPT}$ is the maximum. **Algorithm 2** takes an optimal solution $(v^*_i)$ of $\mathrm{SDP}(0)$ (unit vectors in $\mathbb R^n$ with pairwise nonnegative inner products maximizing $\sum_{E_+}w_{ij}v_i\cdot v_j+\sum_{E_-}w_{ij}(1-v_i\cdot v_j)$), forms $\mathcal C_4=4$-spokes$(v^*)$ and $\mathcal C_5=5$-spokes$(v^*)$, and returns the one of larger value.
--
--   **Theorem 4.5.** For every instance and every optimal solution $v^*$ of $\mathrm{SDP}(0)$,
--   $$\mathbb E\big[\max(\mathrm{val}(\mathcal C_4),\mathrm{val}(\mathcal C_5))\big]\ \ge\ 0.7818\cdot\mathrm{OPT}.$$
--   This improves Swamy's ratio 0.7666 for MaxAgree.
--
--   **Formalization Note.** The conclusion is stated as `0.7818 * val C ≤ algorithm2Value v` for every labelling `C : Fin n → ℕ`, which is equivalent to the bound against $\mathrm{OPT}$. The spokes of $\mathcal C_4$ and $\mathcal C_5$ are independent standard Gaussian vectors; ties go to the least index. The expectation is a Bochner integral against the product Gaussian measure.
--
--   Differences from the source:
--   - encoding: E[val(output)] ≥ 0.7818·OPT, OPT the maximum of val over all clusterings → 0.7818·val(C) ≤ E[max(val C4, val C5)] for every labelling C : Fin n → ℕ; reason: val takes finitely many values, so OPT is attained and the two forms are equivalent; no real supremum
--   - encoding: clusterings of V = {1,…,n} → labellings Fin n → ℕ; reason: every partition is induced by a labelling and val depends only on the partition
--   - encoding: ties in the argmax "may be broken arbitrarily" → least index among the maximizers; reason: ties have probability zero
--   - reading: C4 ← 4-spokes(v*), C5 ← 5-spokes(v*) (coupling of the two runs unspecified) → independent spokes: 4 and 5 independent standard Gaussian vectors in ℝⁿ; reason: Algorithm 2 does not say; fresh randomness per call is the natural reading, and the paper's argument (the maximum dominates the mixture) does not depend on the coupling
-- source:
--   García-Soriano, Miyauchi, Hermite Brings a Laptop, arXiv:2609.35453 (held version, sha256 97504f90…), p. 29 (PDF 32), Theorem 4.5 (Algorithm 2, p. 28 / PDF 31)

import Mathlib
import Definitions.Def_HermiteLaptop_MaxAgree_Instance
import Definitions.Def_HermiteLaptop_MaxAgree_KSpokes

namespace HermiteLaptop.MaxAgree

/-- Theorem 4.5: for MaxAgree, Algorithm 2 (the better of 4-spokes and 5-spokes applied to an
optimal solution of `SDP(0)`) has expected approximation ratio `0.7818`:
`E[max(val C4, val C5)] ≥ 0.7818 · val(C)` for every clustering `C`, hence `≥ 0.7818 · OPT`. -/
theorem theorem_4_5 {n : ℕ} (I : Instance n) (v : Fin n → EuclideanSpace ℝ (Fin n))
    (hv : I.SDPOptimal 0 v) (C : Fin n → ℕ) :
    (0.7818 : ℝ) * I.val C ≤ I.algorithm2Value v := by sorry

end HermiteLaptop.MaxAgree
