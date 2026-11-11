-- Prove2me | Theorems.Thm_MaxCutMatrix2027_Upper_random_submatrix_cut_norm
-- name    : MaxCutMatrix2027.Upper.random_submatrix_cut_norm
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T12:48:03.856573+00:00
-- url     : https://prove2.me/theorems/41d14523-aa1f-4b8a-ad95-c109312cc3e7
-- title:
--   Lemma 4.4 — Random submatrix cut-norm estimate
-- statement:
--   There is one absolute constant $C_{\mathrm{RV}}>0$ such that for every deterministic real square matrix $B$ and every $p\in[0,1]$, if $P$ has independent Bernoulli$(p)$ diagonal entries, then
--   $$\mathbb E\|PBP\|_{\infty\to1}\le C_{\mathrm{RV}}\left(p^2\|B-\operatorname{diag}(B)\|_{\infty\to1}+p\sum_i|B_{ii}|+p^{3/2}(\|B\|_{\mathrm{Col}}+\|B^T\|_{\mathrm{Col}})\right).$$
--   The same selectors occur on both sides of $B$. No symmetry or diagonal restriction is imposed. The constant is chosen before the dimension, matrix and sampling probability. This is the random-restriction estimate used for the spectral residual.
--
--   Differences from the source:
--   - encoding: vertices labelled by [n] and independent Bernoulli selectors → Fin n and the exact finite Bernoulli-subset expectation; reason: relabeling is bijective and the subset weights are exactly the independent-selector law
--   - encoding: p raised to the power 3/2 → p times the square root of p; reason: these coincide for every allowed p, including zero
-- source:
--   Songhua He, STOC 2027 submission #351 (October 2026), Lemma 4.4, p.19 (PDF p.19); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/351.pdf; PDF SHA-256 b38cd84079663d9e2eb7375d7bf1572d5dc7c2157cfaf90e175fd371a9503631

import Definitions.Def_MaxCutMatrix2027_Upper_MatrixModel
set_option autoImplicit false
open scoped BigOperators

namespace MaxCutMatrix2027.Upper

/-- Lemma 4.4, p.19. One absolute constant, all square real matrices and p∈[0,1]. -/
theorem random_submatrix_cut_norm :
    ∃ C_RV : ℝ, 0 < C_RV ∧ ∀ (n : ℕ) (B : Matrix (Fin n) (Fin n) ℝ)
      (p : ℝ), 0 ≤ p → p ≤ 1 →
      sampleAverage p (fun Q => cutNorm (restrictMatrix Q B)) ≤
        C_RV * (p ^ 2 * cutNorm (B - diagonalPart B) +
          p * ∑ i, |B i i| + (p * Real.sqrt p) * (columnNorm B + columnNorm B.transpose)) := by sorry

end MaxCutMatrix2027.Upper
