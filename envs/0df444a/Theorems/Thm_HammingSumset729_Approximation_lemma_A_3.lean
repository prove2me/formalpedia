-- Prove2me | Theorems.Thm_HammingSumset729_Approximation_lemma_A_3
-- name    : HammingSumset729.Approximation.lemma_A_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T12:41:48.772874+00:00
-- url     : https://prove2.me/theorems/030158fd-43eb-4313-8bfd-627313179f6b
-- title:
--   Lemma A.3 — period bounds runs
-- statement:
--   Let $P$ have length $m$, let $0\le k\le m$ be an integer, and let $\ell$ be a positive $8k$-period of $P$ with $\ell\le k$. For each residue modulo $\ell$, form the subsequence of symbols at that residue and count its maximal constant runs. Their sum satisfies
--
--   $$\operatorname{runs}_{\ell}(P)\le9k.$$
--
--   This bounds the column-wise run count used by the small-period kernel branch. Empty subsequences have zero runs.
--
--   Differences from the source:
--   - encoding: the appendix context has k≤m and an 8k-period ℓ≤k → k≤|P|, a positive period bounded by |P|, and ℓ≤k are explicit hypotheses; reason: these are standing assumptions of the bounded-distance kernel; the constants 8 and 9 are unchanged
-- source:
--   Nick Fischer, Yael Kirkpatrick, Vassilios Nakos, STOC 2027 submission #729 (October 2026), Lemma A.3, printed p. 23 (PDF p. 25). https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/729.pdf

import Definitions.Def_HammingSumset729_Approximation_Strings

set_option autoImplicit false
open scoped ENNReal NNReal

namespace HammingSumset729.Approximation

theorem lemma_A_3 {α : Type*} [DecidableEq α] (p : List α) (k ell : ℕ)
    (hk : k ≤ p.length) (hperiod : IsPeriod p (8 * k) ell) (hell : ell ≤ k) :
    runsByPeriod p ell ≤ 9 * k := by sorry

end HammingSumset729.Approximation
