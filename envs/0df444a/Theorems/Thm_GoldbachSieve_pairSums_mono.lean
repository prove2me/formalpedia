-- Prove2me | Theorems.Thm_GoldbachSieve_pairSums_mono
-- name    : GoldbachSieve.pairSums_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T17:39:15.080058+00:00
-- url     : https://prove2.me/theorems/bdc5ea60-e468-4670-813d-82cd4b2339aa
-- title:
--   The small-prime sum set is monotone in all three bounds
-- statement:
--   If $P \le P'$, $lo' \le lo$ and $hi \le hi'$, then with the sieve cutoff fixed,
--
--   $$C(P, lo, hi, c) \subseteq C(P', lo', hi', c).$$
--
--   Here $C(P,lo,hi,c)$ is the set of sums $p + q$ with $p \le P$ prime and $q$ a survivor in $[lo,hi]$. Enlarging the prime bound, lowering the lower endpoint and raising the upper endpoint can only add sums, so every element of the smaller set lies in the larger.
--
--   **Why it matters.** This is the direction in which coverage is actually used: a certificate established for one prime bound and one interval covers every smaller prime bound and every sub-interval, so a single verified block serves all the narrower obligations inside it. Without it, each sub-interval obligation would need its own certificate.
--
--   **Formalization Note.** Combines `GoldbachSieve.mem_pairSums` with `GoldbachSieve.survivors_mono`.
-- source:
--   GoldbachSieve.pairSums (platform definition); Richstein 2001 segmented sieve, block and sub-interval transfers.

import Definitions.Def_GoldbachSieve

namespace GoldbachSieve

theorem pairSums_mono {P P' lo lo' hi hi' c : ℕ} (hP : P ≤ P') (hlo : lo' ≤ lo) (hhi : hi ≤ hi') :
    pairSums P lo hi c ⊆ pairSums P' lo' hi' c := by sorry

end GoldbachSieve
