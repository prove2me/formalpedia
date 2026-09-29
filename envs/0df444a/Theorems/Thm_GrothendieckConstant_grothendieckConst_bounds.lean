-- Prove2me | Theorems.Thm_GrothendieckConstant_grothendieckConst_bounds
-- name    : GrothendieckConstant.grothendieckConst_bounds
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-23T18:58:23.41099+00:00
-- url     : https://prove2.me/theorems/0539d3ea-d27f-4cc5-aedf-e47b49885390
-- title:
--   $\frac{6\pi}{11}\le K_G\le\frac{\pi}{2\log(1+\sqrt2)}-3.47\times10^{-4}$
-- statement:
--   **The two-sided bound of the source paper.** Combining its Theorem 2.2 (lower) and Theorem 2.1 (upper), the Grothendieck constant satisfies
--
--   $$\frac{6\pi}{11}\ \le\ K_G\ \le\ \frac{\pi}{2\log(1+\sqrt2)}-3.47\times10^{-4},$$
--
--   that is $1.7135\ldots\le K_G\le1.7818\ldots$, which determines the tenths digit of $K_G$ to be $7$.
--
--   Recall that $K_G$ is the least constant $K$ with $\mathrm{SDP}(A)\le K\cdot\mathrm{OPT}(A)$ for every real matrix $A$, where $\mathrm{OPT}$ maximizes the bilinear form over $\pm1$ labelings and $\mathrm{SDP}$ over unit vectors of arbitrary dimension. The previous state of the art was $1.6769\ldots\le K_G\le1.7822\ldots$, an interval in which even the tenths digit was undetermined. The lower half is the first bound on $K_G$ proved without constructing a hard instance; the upper half is the first improvement on Krivine's bound obtained from a scheme of growing rather than fixed dimension.
--
--   Here $\log$ denotes the natural logarithm.
-- source:
--   Li, Saha, Xue, Chaudhuri, Klivans, Kothari, Meka, "Long-Horizon AI Research for Grothendieck Constant: A Case Study in Human-AI Mathematical Collaboration", arXiv:2608.11195v3 (2026), https://arxiv.org/abs/2608.11195, Section 2, p. 6: "Together, the two theorems give 6 pi / 11 <= K_G <= pi / (2 log(1 + sqrt 2)) - 3.47 x 10^{-4}, determining the tenths digit of K_G to be 7." (Theorems 2.1 and 2.2, abridged; full proofs in the companion paper, Saha et al., 2026.)

import Mathlib
import Definitions.Def_GrothendieckConstantDefs

namespace GrothendieckConstant

theorem grothendieckConst_bounds :
    6 * Real.pi / 11 ≤ grothendieckConst ∧
      grothendieckConst ≤
        Real.pi / (2 * Real.log (1 + Real.sqrt 2)) - 3.47 * 10 ^ (-4 : ℤ) := by sorry

end GrothendieckConstant
