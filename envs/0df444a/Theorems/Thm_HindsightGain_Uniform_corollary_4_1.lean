-- Prove2me | Theorems.Thm_HindsightGain_Uniform_corollary_4_1
-- name    : HindsightGain.Uniform.corollary_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:52:42.897064+00:00
-- url     : https://prove2.me/theorems/aee6a24b-32b6-44c3-ad1b-9eb76fa1d49a
-- title:
--   Corollary 4.1 — Thinning a fixed set
-- statement:
--   Fix integers $n,D\ge1$, $r\ge2$ and a model $(K,A)$ as in Section 1.1. Let $U\subseteq[n]$, $s\in[0,1]$, and let $U_s$ independently retain each element of $U$ with probability $s$. Write $A_U$ for the interactions retained inside $U$ and $(m)_k$ for the falling factorial. Then
--   $$0\le\mathbb E\operatorname{Val}_A(U_s)-s^r\operatorname{Val}_A(U)\le r\sqrt5\,s^{r/2}\sqrt{1-s}\sqrt{(|U|)_{r-1}}\,\|A_U\|_F.$$
--   Both endpoints $s=0,1$ and every set $U$, including the empty set or $|U|<r$, are included. The exact falling factorial keeps the active-variable dependence needed by the next thinning statement.
--
--   Differences from the source:
--   - encoding: arbitrary multilinear interactions on r-element subsets of [n] and Euclidean local domains → coefficient arrays on cardinality-r Finsets of Fin n, with each interaction evaluated in increasing order in EuclideanSpace ℝ (Fin D); reason: orthonormal coordinates encode every source multilinear map uniquely, preserving its coefficient Frobenius norm and every compact local domain
--   - encoding: a maximum over the compact product domain → the real sSup of the actual polynomial image; reason: Model includes all source nonemptiness and compactness assumptions, so the image is nonempty, compact, bounded and has an attained maximum
--   - encoding: expectation over independent retention inside U or [n] → the finite sum over subsets S of U with mass p^|S| (1-p)^(|U|-|S|); reason: this is exactly the independent Bernoulli retention law, including p = 0 and p = 1 with the usual zeroth-power convention
--   - encoding: half-integer real powers and the falling factorial (m)_(r-1) → real powers with real exponents and the real cast of Nat.descFactorial m (r-1); reason: all divisions in exponents occur after casting, and the falling factorial is zero when m < r-1
-- source:
--   Xiaohui Bei, Wenhao Wu, The Optimizer's Windfall: Bounding Hindsight Gain under Random Restrictions, STOC 2027 submission #464 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/464.pdf, Corollary 4.1, (26), p.19

import Mathlib
import Definitions.Def_HindsightGain_Uniform_optima

set_option autoImplicit false

namespace HindsightGain.Uniform

/-- Corollary 4.1 (26), p.19, including empty U and both endpoints of [0,1]. -/
theorem corollary_4_1 {n D r : ℕ} (M : Model n D r) (U : Finset (Fin n))
    (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    0 ≤ thinningMean M U s - s ^ r * setVal M U ∧
      thinningMean M U s - s ^ r * setVal M U ≤
        (r : ℝ) * Real.sqrt 5 * s ^ ((r : ℝ) / 2) * Real.sqrt (1 - s) *
          Real.sqrt (Nat.descFactorial U.card (r - 1) : ℝ) * frobenius (restrict M U) := by sorry

end HindsightGain.Uniform
