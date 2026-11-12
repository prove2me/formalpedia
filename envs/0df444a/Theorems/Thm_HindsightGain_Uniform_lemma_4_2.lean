-- Prove2me | Theorems.Thm_HindsightGain_Uniform_lemma_4_2
-- name    : HindsightGain.Uniform.lemma_4_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-08T10:51:42.076526+00:00
-- url     : https://prove2.me/theorems/b9423f26-329c-4bde-b00f-5455dc39e9ef
-- title:
--   Lemma 4.2 — One thinning step
-- statement:
--   Fix integers $n,D\ge1$, $r\ge2$ and a model $(K,A)$ as in Section 1.1. For $u\in(0,1]$, let $F_A(u)=u^{-r}\mathbb E\operatorname{Val}_A(S_u)$, where $S_u$ independently retains each variable with probability $u$. For every $s,t\in(0,1]$,
--   $$0\le F_A(st)-F_A(t)\le r\sqrt5\,\frac{\sqrt{1-s}}{s^{r/2}}\,t^{-1/2}\sqrt{(n)_{r-1}}\,\|A\|_F.$$
--   Here $(n)_{r-1}$ is the exact falling factorial. Sampling rates may be arbitrarily small; no condition on $stn$ is imposed. This quantifies the change of the compensated optimum under one further thinning.
--
--   Differences from the source:
--   - encoding: arbitrary multilinear interactions on r-element subsets of [n] and Euclidean local domains → coefficient arrays on cardinality-r Finsets of Fin n, with each interaction evaluated in increasing order in EuclideanSpace ℝ (Fin D); reason: orthonormal coordinates encode every source multilinear map uniquely, preserving its coefficient Frobenius norm and every compact local domain
--   - encoding: a maximum over the compact product domain → the real sSup of the actual polynomial image; reason: Model includes all source nonemptiness and compactness assumptions, so the image is nonempty, compact, bounded and has an attained maximum
--   - encoding: expectation over independent retention inside U or [n] → the finite sum over subsets S of U with mass p^|S| (1-p)^(|U|-|S|); reason: this is exactly the independent Bernoulli retention law, including p = 0 and p = 1 with the usual zeroth-power convention
--   - encoding: half-integer real powers and the falling factorial (m)_(r-1) → real powers with real exponents and the real cast of Nat.descFactorial m (r-1); reason: all divisions in exponents occur after casting, and the falling factorial is zero when m < r-1
-- source:
--   Xiaohui Bei, Wenhao Wu, The Optimizer's Windfall: Bounding Hindsight Gain under Random Restrictions, STOC 2027 submission #464 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/464.pdf, Lemma 4.2 and (27), p.20

import Mathlib
import Definitions.Def_HindsightGain_Uniform_optima

set_option autoImplicit false

namespace HindsightGain.Uniform

/-- Lemma 4.2, p.20: the exact falling factorial, at all positive sampling rates. -/
theorem lemma_4_2 {n D r : ℕ} (M : Model n D r)
    (s t : ℝ) (hs0 : 0 < s) (hs1 : s ≤ 1) (ht0 : 0 < t) (ht1 : t ≤ 1) :
    0 ≤ compensated M (s * t) - compensated M t ∧
      compensated M (s * t) - compensated M t ≤
        (r : ℝ) * Real.sqrt 5 * (Real.sqrt (1 - s) / s ^ ((r : ℝ) / 2)) *
          t ^ (-(1 : ℝ) / 2) * Real.sqrt (Nat.descFactorial n (r - 1) : ℝ) *
            frobenius M := by sorry

end HindsightGain.Uniform
