-- Prove2me | Theorems.Thm_GoldbachSieve_survivors_mono
-- name    : GoldbachSieve.survivors_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T17:39:15.231916+00:00
-- url     : https://prove2.me/theorems/096d93f5-b191-4d4d-910e-c101dec10262
-- title:
--   Survivors are monotone: widening the interval keeps every survivor
-- statement:
--   With the sieve cutoff fixed, if the interval $[lo, hi]$ is contained in $[lo', hi']$, then
--
--   $$S(lo, hi, c) \subseteq S(lo', hi', c).$$
--
--   Survivorship is a property of $q$ relative to an interval and a cutoff: $q$ lies in the interval and has no proper prime divisor at most $c$. Widening the interval preserves both conditions, since $\max(2,lo') \le \max(2,lo)$ and $hi \le hi'$.
--
--   **Why it matters.** Coverage statements are proved on sub-intervals and wanted on larger ones, or the reverse: a certificate on a block transfers to any interval inside it. This lemma is that transfer, and it is the only interval reasoning that such transfers need.
--
--   **Formalization Note.** Follows from `GoldbachSieve.mem_survivors` by monotonicity of $\max(2,\cdot)$.
-- source:
--   GoldbachSieve.survivors (platform definition); Richstein 2001 segmented sieve, interval bookkeeping.

import Definitions.Def_GoldbachSieve

namespace GoldbachSieve

theorem survivors_mono {lo lo' hi hi' c : ℕ} (h1 : lo' ≤ lo) (h2 : hi ≤ hi') :
    survivors lo hi c ⊆ survivors lo' hi' c := by sorry

end GoldbachSieve
