-- Prove2me | Theorems.Thm_OnlineRealSampling_Exact_proposition_3_1
-- name    : OnlineRealSampling.Exact.proposition_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:21:31.569913+00:00
-- url     : https://prove2.me/theorems/cfd1b819-c771-473b-a6ee-e0711f49b78d
-- title:
--   Proposition 3.1 — ApproxDivision in $O(k)$ time
-- statement:
--   Let $q=a/b\in[0,1]$, given as integers $0\le a\le b$ with $b>0$, and let $k\ge1$. Algorithm 4 returns integers $a',b'$ with
--   $$\Big|\frac ab-\frac{a'}{b'}\Big|<2^{-k},\qquad 0\le a'\le b'<2^{k+1},\qquad b'>0,$$
--   and its word-RAM time is at most $Kk$ for an absolute constant $K$, however long $a$ and $b$ are.
--
--   ApproxDivision is what lets IntervalSample use the random state $(Z,M)$ at precision $t$ without paying for the length of $M$.
--
--   Differences from the source:
--   - encoding: input q = a/b ∈ [0,1]; output a rational a'/b' → natural numbers a ≤ b with b > 0; the returned pair also satisfies 0 < b'; reason: a rational is a pair with positive denominator; nonnegative representatives of q ∈ [0,1]
--   - generalization: O(·) bounds for a fixed word size w ≥ 1 → one constant K valid for every word size w ≥ 1; reason: the source's constants do not depend on w; the statement specializes to each fixed w
--   - reading: Word RAM in which big-integer multiplication and division cost O(k log k) or Θ(k²) → concrete charged primitives: addition, subtraction and comparison cost limbs(a)+limbs(b); multiplication and division cost limbs(a)·limbs(b)+limbs(a)+limbs(b); shifts and powers of two cost the limbs of the result plus 1; bit length costs 1; every machine step costs at least 1; reason: the source leaves the multiplication algorithm open and names schoolbook as one option; C_F is assumed to dominate basic arithmetic under either choice
-- source:
--   Draper, Harris & Saad, Online Random Sampling with Real Probabilities, STOC 2027 submission #103, preprint dated 2026-11-02 (source.pdf sha256 66aeb5c181baf97cefba69aa26d29299e888a7a86c837a71af5b77d35f11c3e1; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/103.pdf), Proposition 3.1, PDF 7 / printed 6; Algorithm 4 and proof in Appendix A, PDF 19 / printed 18

import Mathlib
import Definitions.Def_OnlineRealSampling_Exact_Algorithms

open MeasureTheory
open scoped ENNReal

namespace OnlineRealSampling.Exact

/-- Proposition 3.1 (ApproxDivision). For `q = a/b ∈ [0,1]` and `k ≥ 1`, Algorithm 4 returns
`q' = a'/b'` with `|q - q'| < 2^{-k}` and `0 ≤ a' ≤ b' < 2^{k+1}`, in `O(k)` word time, however
long `a` and `b` are. -/
theorem proposition_3_1 :
    ∃ K : ℝ, ∀ w : ℕ, 1 ≤ w → ∀ a b k : ℕ, 0 < b → a ≤ b → 1 ≤ k →
      |(a : ℝ) / b - ((approxDivision w a b k).val.1 : ℝ) / (approxDivision w a b k).val.2|
          < 1 / 2 ^ k ∧
        0 ≤ (approxDivision w a b k).val.1 ∧
        (approxDivision w a b k).val.1 ≤ (approxDivision w a b k).val.2 ∧
        (approxDivision w a b k).val.2 < 2 ^ (k + 1) ∧
        0 < (approxDivision w a b k).val.2 ∧
        ((approxDivision w a b k).led.time : ℝ) ≤ K * k := by sorry

end OnlineRealSampling.Exact
