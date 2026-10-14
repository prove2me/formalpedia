-- Prove2me | Theorems.Thm_IntMul_HvdH_coprime_params
-- name    : IntMul.HvdH.coprime_params
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-11T21:32:19.17599+00:00
-- url     : https://prove2.me/theorems/1c701b93-cb03-4c7f-82a9-fe73a94a7690
-- title:
--   Pairwise coprime odd $s_i\in((1-2\eta)t_i,(1-\eta)t_i]$, $\eta=1/4d$ (replacement for HvdH Lemma 5.1)
-- statement:
--   Let $d\ge1$, $0\le d'\le d$, and let $r$ be even with $r\ge 64d^2\,(256d^2)!$. Put $\eta=1/(4d)$ and $t_i=r/2$ for $i<d'$, $t_i=r$ for $d'\le i<d$. Then there are odd, pairwise coprime natural numbers $s_0,\dots,s_{d-1}$ with
--   $$(1-2\eta)\,t_i<s_i\le(1-\eta)\,t_i\qquad\text{for all }i .$$
--   This is exactly what Harvey–van der Hoeven need from the primes of Lemma 5.1 in §5.1 (condition (5.11)). Oddness gives $\gcd(s_i,t_i)=1$ for powers of two $t_i$, and pairwise coprimality is what the Agarwal–Cooley step needs. The proof uses no prime number theory: the $s_i$ have the form $1+Qm$ with $(256d^2)!\mid Q$ and all $m\le 256d^2$. In the paper's setting $r\ge2^{d^{10}}$, which is far larger than the hypothesis needs.
--
--   *Formalization note.* The interval conditions are stated in integers: $(4d-2)t_i<4d\,s_i\le(4d-1)t_i$.
-- source:
--   Harvey, van der Hoeven, Integer multiplication in time O(n log n), Annals of Math. 193 (2021), https://hal.science/hal-02070778, Section 5.1 (Lemma 5.1 and condition (5.11)); elementary replacement

import Mathlib

namespace IntMul.HvdH
theorem coprime_params (d d' r : ℕ) (hd : 1 ≤ d) (hd' : d' ≤ d) (hr : 2 ∣ r)
    (hbig : 64 * d ^ 2 * (256 * d ^ 2).factorial ≤ r) :
    ∃ s : Fin d → ℕ, (∀ i, Odd (s i)) ∧ (∀ i j, i ≠ j → Nat.Coprime (s i) (s j)) ∧
      ∀ i : Fin d, (4 * d - 2) * (if (i : ℕ) < d' then r / 2 else r) < 4 * d * s i ∧
        4 * d * s i ≤ (4 * d - 1) * (if (i : ℕ) < d' then r / 2 else r) := by sorry
end IntMul.HvdH
