-- Prove2me | Theorems.Thm_GoldbachSieve_mem_survivors
-- name    : GoldbachSieve.mem_survivors
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T11:03:06.958387+00:00
-- url     : https://prove2.me/theorems/6c77220a-f123-499c-a04e-cc8670d2b94f
-- title:
--   A sieve survivor is exactly a number in the interval with no proper prime divisor up to the cutoff
-- statement:
--   For bounds $lo$, $hi$ and a sieve cutoff $c$, a number $q$ is a *survivor*,
--
--   $$q \in S(lo,hi,c),$$
--
--   exactly when
--
--   $$\max(2, lo) \le q \le hi \quad\text{and}\quad \forall r,\ \bigl(r \text{ prime} \wedge r \le c \wedge r \mid q\bigr) \Rightarrow r = q .$$
--
--   That is, $q$ lies in the interval and has no prime divisor at most $c$ other than possibly itself.
--
--   **Why it matters.** The sieve obligations on this platform are stated in two forms: as membership in the finite set $S(lo,hi,c)$, and as the raw divisibility condition on a number $q$. Both forms appear side by side in Richstein's segmented-sieve family, and a proof of one form cannot be used where the other is expected. This theorem is the dictionary between them: it turns a `Finset` membership into a divisibility statement, and with it a number known to be prime is immediately a survivor (take $r \mid q$ with $r$ prime; then $r = q$).
--
--   **Formalization Note.** The definition `GoldbachSieve.survivors` counts the sieving primes that divide $q$ properly and keeps $q$ when that count is zero; the proof converts the vanishing count into the pointwise statement by `Finset.card_eq_zero` and back by exhibiting an element of positive count.
-- source:
--   GoldbachSieve.survivors (platform definition, Richstein 2001 segmented sieve); bridges the two statement forms used by Richstein2001.segmented_sieve_block_witnesses and TaoFivePrimes.goldbach_sieve_witness_to_primes.

import Definitions.Def_GoldbachSieve

namespace GoldbachSieve

theorem mem_survivors {lo hi c q : ℕ} :
    q ∈ survivors lo hi c ↔
      max 2 lo ≤ q ∧ q ≤ hi ∧ ∀ r : ℕ, r.Prime → r ≤ c → r ∣ q → r = q := by sorry

end GoldbachSieve
