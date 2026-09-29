-- Prove2me | Theorems.Thm_OddPerfectNumber_touchard
-- name    : OddPerfectNumber.touchard
-- status  : Proved
-- author  : @Gabewhigham
-- created : 2026-09-07T20:16:16.567821+00:00
-- url     : https://prove2.me/theorems/9b464ce9-8fd0-4ddf-afaf-8ef2d0890816
-- title:
--   Touchard: an odd perfect number is $\equiv 1 \pmod{12}$ or $\equiv 9 \pmod{36}$
-- statement:
--   **Touchard's theorem (1953).** Every odd perfect number $N$ satisfies
--   $$N \equiv 1 \pmod{12} \qquad \text{or} \qquad N \equiv 9 \pmod{36}.$$
--
--   Equivalently, an odd perfect number is congruent to $1$ modulo $12$, or is divisible by $9$ but not by $4$ and congruent to $9$ modulo $36$. The theorem rules out, for instance, $N \equiv 5, 7, 11 \pmod{12}$. Touchard's original proof is intricate; short proofs were given by Satyanarayana (1959) and by Holdener (2002), the latter deriving the result from Euler's form together with elementary congruence bookkeeping for $\sigma$.
--
--   Formalized as `n % 12 = 1 ∨ n % 36 = 9` for natural numbers.
-- source:
--   J. Touchard, On prime numbers and perfect numbers, Scripta Mathematica 19 (1953), 35-39; short proof in J. A. Holdener, A theorem of Touchard on the form of odd perfect numbers, Amer. Math. Monthly 109 (2002), 661-663.

import Mathlib

namespace OddPerfectNumber

theorem touchard (n : ℕ) (hn : Nat.Perfect n) (hodd : Odd n) : n % 12 = 1 ∨ n % 36 = 9 := by
  sorry

end OddPerfectNumber
