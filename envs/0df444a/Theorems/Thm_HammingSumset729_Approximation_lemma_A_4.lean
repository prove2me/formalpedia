-- Prove2me | Theorems.Thm_HammingSumset729_Approximation_lemma_A_4
-- name    : HammingSumset729.Approximation.lemma_A_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T12:41:53.459477+00:00
-- url     : https://prove2.me/theorems/6f5ea736-f6aa-41d7-83d5-38ca75b27418
-- title:
--   Lemma A.4 — trim text without losing close occurrences
-- statement:
--   Let $|P|=m$, $|T|=2m$, $0\le k\le m$, and let $\ell\le k$ be a positive $8k$-period of $P$. Construct $T_L$ as the longest suffix of the first length-$m$ half of $T$ whose column-wise run count is at most $11k$. Construct $T_R$ as the longest prefix of the second half with the same bound. Every valid shift $i$ with distance at most $k$ satisfies
--
--   $$m-|T_L|\le i,\qquad i+m\le m+|T_R|.$$
--
--   Thus the original window is geometrically contained in the specific trim $T_L T_R$. The suffix and prefix are constructed from the input, rather than supplied as arbitrary witnesses.
--
--   Differences from the source:
--   - encoding: the bounded-distance kernel context and containment of the original window in the constructed trim → |T|=2|P|, k≤|P|, the 8k-period ℓ≤k, and inequalities for the original window endpoints; reason: the longest suffix and prefix are computed from T with the exact 11k budgets; geometric containment is equivalent to the source conclusion
-- source:
--   Nick Fischer, Yael Kirkpatrick, Vassilios Nakos, STOC 2027 submission #729 (October 2026), Lemma A.4, printed p. 23 (PDF p. 25). https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/729.pdf

import Definitions.Def_HammingSumset729_Approximation_Strings

set_option autoImplicit false
open scoped ENNReal NNReal

namespace HammingSumset729.Approximation

theorem lemma_A_4 {α : Type*} [DecidableEq α] (t p : List α) (k ell : ℕ)
    (hlen : t.length = 2 * p.length) (hk : k ≤ p.length)
    (hperiod : IsPeriod p (8 * k) ell) (hell : ell ≤ k)
    (i : ℕ) (hi : i ≤ p.length) (hclose : shiftDistance t p i ≤ k) :
    p.length - (trimmedLeft t p.length ell k).length ≤ i ∧
      i + p.length ≤ p.length + (trimmedRight t p.length ell k).length := by sorry

end HammingSumset729.Approximation
