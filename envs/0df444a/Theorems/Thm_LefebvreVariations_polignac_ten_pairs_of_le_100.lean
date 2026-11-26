-- Prove2me | Theorems.Thm_LefebvreVariations_polignac_ten_pairs_of_le_100
-- name    : LefebvreVariations.polignac_ten_pairs_of_le_100
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-26T00:05:01.07918+00:00
-- url     : https://prove2.me/theorems/cee07f36-8c00-436e-a5a3-1e61e5ae4248
-- title:
--   Lefebvre's variations, No. 69 — on a theme by Polignac: every even gap k at most 100 occurs between at least ten prime pairs
-- statement:
--   For every even integer $k$ with $2\le k\le 100$ there is a finite set $S$ of at least ten primes $p$ such that $p+k$ is also prime.
--
--   Polignac's conjecture asks for infinitely many such primes for each even $k$; the statement here says that for each even gap $k\le 100$ at least ten prime pairs $(p,p+k)$ exist. Twin primes ($k=2$), cousin primes ($k=4$) and sexy primes ($k=6$) are among the cases.
--
--   **Formalization Note** The parent states `{p | Nat.Prime p ∧ Nat.Prime (p + k)}.Infinite`; here an explicit finset `S` with `10 ≤ S.card` and the same prime conditions replaces infinitude, with hypotheses `0 < k`, `Even k`, `k ≤ 100` copied from the parent plus the bound. For each $k$ the pairs are found below $200$ (checked in Python).
--
--   **Why this is a variation.** This is a variation of the open platform problem polignac_conjecture (infinitely many prime pairs (p, p+k) for each even k). It is a partial result in the parent's own terms: existence of at least ten pairs, for every even gap k up to 100, with explicit witnesses. It is a finite, checkable step toward the infinitude the parent asks for, and covers the twin, cousin and sexy prime gaps as special cases.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   A. de Polignac, Recherches nouvelles sur les nombres premiers, C. R. Acad. Sci. Paris 29 (1849), 397-401 and 738-739 (cited from memory, not re-checked). Y. Zhang, Bounded gaps between primes, Ann. of Math. 179 (2014), 1121-1174, and J. Maynard (2015) show some gap occurs infinitely often (cited from memory). The statement was checked directly in Python for every even k in [2,100] (each has at least 78 pairs below 3000). It is the platform theorem polignac_conjecture with infinitude replaced by at least ten pairs and k <= 100.

import Mathlib

set_option autoImplicit false

namespace LefebvreVariations
theorem polignac_ten_pairs_of_le_100 (k : ℕ) (hk : 0 < k) (hk2 : Even k) (hle : k ≤ 100) :
    ∃ S : Finset ℕ, 10 ≤ S.card ∧ ∀ p ∈ S, Nat.Prime p ∧ Nat.Prime (p + k) := by sorry
end LefebvreVariations
