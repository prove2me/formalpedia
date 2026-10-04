-- Prove2me | Theorems.Thm_OddPerfectNumber_Kernel_five_euler_prime_is_five_mod_forty_eight
-- name    : OddPerfectNumber.Kernel.five_euler_prime_is_five_mod_forty_eight
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-02T12:09:52.09689+00:00
-- url     : https://prove2.me/theorems/0d5a698d-616f-449d-87f5-b9829a782d2c
-- title:
--   In the $k=5$ residual the Euler prime is $5 \pmod{48}$
-- statement:
--   Suppose the $k=5$ two-prime residual has already forced $p+1 = 6u^2$ for some $u$, as the proved theorem `five_euler_index_is_six_times_square` establishes from $B = 3^{2k+1}v^2$. Then together with the Euler-prime hypothesis $p \equiv 1 \pmod 4$ one obtains the much sharper restriction
--
--   $$p \equiv 5 \pmod{48}.$$
--
--   Indeed $p \equiv 1 \pmod 4$ forces $u^2$ odd, so $u$ is odd, and an odd square is $1$ modulo $8$. Hence $p+1 = 6u^2 \equiv 6 \pmod{48}$, i.e. $p \equiv 5 \pmod{48}$.
--
--   **Consequence.** This upgrades the earlier parity-only conclusion $p \equiv 5 \pmod{12}$ to a congruence modulo $48$, and it is the first point at which the square structure of the linear cyclotomic factor $(p+1)/2$ feeds back into the Euler prime itself. Two further consequences follow immediately and are recorded as separate targets: $p \equiv 5 \pmod 8$ gives $p^2+p+1 \equiv 7 \pmod 8$ and $(p^2-p+1)/3 \equiv 7 \pmod 8$, which through the proved allocation $C = q u_1^2$ and $D_0 = r u_2^2$ transfer to $q \equiv r \equiv 7 \pmod 8$ and hence, with the mod-$3$ transfer, $q \equiv r \equiv 7 \pmod{24}$. Verified exhaustively for every prime $p < 200000$ with $p+1 = 6u^2$ and $p \equiv 1 \pmod 4$: 25 cases, no counterexample.
-- source:
--   Elementary modular arithmetic. Verified exhaustively over all primes $p < 200000$ with $p+1 = 6u^2$ and $p \equiv 1 \pmod 4$ (25 cases, no counterexample). Research note: missions/Odd Perfect Number Conjecture/artefacts/opn/kernel5_20260928/NOTES.md, 'CONSEQUENCE 2 (the mod-24 claim, now derived rather than trusted)'.

namespace OddPerfectNumber.Kernel

/-- If `p % 4 = 1` and `p + 1 = 6 * u ^ 2` for some `u`, then `p % 48 = 5`.

  From `p % 4 = 1` we get `u ^ 2` odd, hence `u` odd, and every odd square is `1 (mod 8)`.
  So `p + 1 = 6 * u ^ 2 = 6 (mod 48)`, giving `p = 5 (mod 48)`. -/
theorem five_euler_prime_is_five_mod_forty_eight (p u : Nat) (hp4 : p % 4 = 1)
    (hshape : p + 1 = 6 * u ^ 2) :
    p % 48 = 5 := by
  sorry

end OddPerfectNumber.Kernel
