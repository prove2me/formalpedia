-- Prove2me | Theorems.Thm_OddPerfectNumber_Kernel_five_middle_block_seven_mod_eight
-- name    : OddPerfectNumber.Kernel.five_middle_block_seven_mod_eight
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-02T12:27:05.900424+00:00
-- url     : https://prove2.me/theorems/559aaf15-ad09-4a63-8fe1-089251823d21
-- title:
--   When $p = 5 \pmod 8$ the first cyclotomic block is $7 \pmod 8$
-- statement:
--   If $p \equiv 5 \pmod 8$ then the first $k=5$ cyclotomic block satisfies $p^2+p+1 \equiv 7 \pmod 8$.
--
--   Indeed $p^2 \equiv 25 \equiv 1 \pmod 8$, so $p^2+p+1 \equiv 1+5+1 = 7 \pmod 8$.
--
--   **Consequence for the $k=5$ two-prime residual.** The proved normalisation gives the first block as $C = q\,u_1^2$ for one of the two square-free index primes $q$, and $C$ is odd, so $u_1$ is odd and $u_1^2 \equiv 1 \pmod 8$. Hence $q \equiv C \equiv 7 \pmod 8$. This is the input that, together with the analogous statement for the normalised second block $(p^2-p+1)/3$, turns the already-proved transfer lemma `five_odd_index_prime_mod_twenty_four` into the concrete conclusion $q \equiv r \equiv 7 \pmod{24}$.
-- source:
--   Elementary modular arithmetic, verified for every prime $p < 200000$ with $p+1 = 6u^2$, $u$ odd (25 cases, no counterexample). Research note: missions/Odd Perfect Number Conjecture/artefacts/opn/kernel5_20260928/NOTES.md, 'CONSEQUENCE 2 (the mod-24 claim, now derived rather than trusted)'.

namespace OddPerfectNumber.Kernel

/-- If `p % 8 = 5` then `p ^ 2 + p + 1 = 7 (mod 8)`.  Writing `p = 8k + 5`,
  `p ^ 2 = 64k^2 + 80k + 25`, so the block is `64k^2 + 88k + 31`, which is `7 (mod 8)`. -/
theorem five_middle_block_seven_mod_eight (p : Nat) (hp8 : p % 8 = 5) :
    (p ^ 2 + p + 1) % 8 = 7 := by
  sorry

end OddPerfectNumber.Kernel
