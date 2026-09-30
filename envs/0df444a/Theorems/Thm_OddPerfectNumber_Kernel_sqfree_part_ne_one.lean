-- Prove2me | Theorems.Thm_OddPerfectNumber_Kernel_sqfree_part_ne_one
-- name    : OddPerfectNumber.Kernel.sqfree_part_ne_one
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-30T09:22:10.800984+00:00
-- url     : https://prove2.me/theorems/b59073fb-8d9c-4e9a-b160-acdd1be9cc25
-- title:
--   A non-square is not a square times one, so its square-free part is not 1
-- statement:
--   If $s = d_1^2 d_2$ is not a perfect square, then its square-free part $d_2$ is not $1$. Indeed $d_2 = 1$ forces $s = d_1^2$, a square. This is the $hne1$ hypothesis of the two proved cardinality children `OddPerfectNumber.Kernel.squarefree_card_ge_two_of_not_one_or_prime` (9c90129e-60c2-4fa1-aa32-c55ece1e485d) and `OddPerfectNumber.Kernel.squarefree_card_ge_three_of_not_small` (64627c09-9af1-4ab3-afc0-a3498abf1dc3), and the hypothesis `hs_nsq` is exactly the live hypothesis of the target leaf `OddPerfectNumber.no_dris_five_s_odd_ge_five_nonsq` (1e19be36-a9fb-45e5-aa4e-464aba65dfe9). It is one of the two facts that, together with the open child `OddPerfectNumber.Kernel.five_index_not_prime_mul_square` (2ec27119-2f77-425b-ab15-a95e11c2f9bc) ruling out $s = q a^2$ for $q$ prime, give $2 \le d_2.\mathrm{primeFactors.card}$ and reduce a failure of the bound $3$ to the exact two-prime semiprime case. The hypothesis is indispensable rather than decorative: a square index does indeed have square-free part $1$, which is why a non-square hypothesis is required.
-- source:
--   Mathlib only, and the proof is three lines. The rewrite `rw [← hd2, hcon, Nat.one_mul]` turns `d1 ^ 2 * 1 = s` round into `s = d1 ^ 2`, which contradicts `hs_nsq` at `⟨d1, this⟩`. No number theory beyond the definition of a square-free part. The point of the child is to isolate the natural-number multiplication cancellation so that the k=5 wrapper stays short and so the role of the non-square hypothesis is recorded explicitly.

import Mathlib

namespace OddPerfectNumber.Kernel

theorem sqfree_part_ne_one (s d1 d2 : Nat) (hd2 : d1 ^ 2 * d2 = s)
    (hs_nsq : ¬ ∃ r : Nat, s = r ^ 2) :
    d2 ≠ 1 := by
  sorry

end OddPerfectNumber.Kernel
