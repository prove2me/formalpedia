-- Prove2me | Theorems.Thm_OddPerfectNumber_zmod_pow_eq_one_iff
-- name    : OddPerfectNumber.zmod_pow_eq_one_iff
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-11T10:13:56.131136+00:00
-- url     : https://prove2.me/theorems/890d5806-d6f3-4d4c-8ec3-42d96f9b4165
-- title:
--   Modular power bridge
-- statement:
--   The congruence $p^n \equiv 1 \pmod q$ in $\mathbf{Z}/q$ is equivalent to the divisibility $q \mid p^n - 1$ in $\mathbf{N}$. Extracted as a standalone lemma from the accepted proof of $\mathtt{no\_dris\_five\_s\_odd\_eq\_three}$ (DHP toolkit); the bridge between modular-order and divisibility arguments.
-- source:
--   DHP toolkit of the accepted Prove2Me proof of OddPerfectNumber.no_dris_five_s_odd_eq_three; Euler structure theorem (L. Euler, De numeris amicabilibus, Opera postuma 1 (1849)).

import Mathlib

namespace OddPerfectNumber

theorem zmod_pow_eq_one_iff {q p n : Nat} (hp : 1 ≤ p) :
    ((p : ZMod q) ^ n = 1) ↔ q ∣ p ^ n - 1 := by
  sorry

end OddPerfectNumber
