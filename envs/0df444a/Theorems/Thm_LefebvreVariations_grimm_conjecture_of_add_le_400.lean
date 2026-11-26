-- Prove2me | Theorems.Thm_LefebvreVariations_grimm_conjecture_of_add_le_400
-- name    : LefebvreVariations.grimm_conjecture_of_add_le_400
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-26T00:04:24.830427+00:00
-- url     : https://prove2.me/theorems/989c7888-184b-5ef4-9b32-42cf085ec427
-- title:
--   Lefebvre's variations, No. 76 — on a theme by Grimm: Grimm's conjecture holds for runs of composites below 400
-- statement:
--   Let $n\ge 2$ and $m\ge 1$ be integers with $n+m\le 400$ such that $n,n+1,\dots,n+m$ are all composite. Then there are pairwise distinct primes $p_0,\dots,p_m$ with $p_i\mid n+i$ for every $i$.
--
--   This is Grimm's conjecture on consecutive composite numbers, restricted to runs lying entirely below $400$.
--
--   **Formalization Note** The conclusion is copied from the parent `grimm_conjecture`: an injective `f : Fin (m + 1) → ℕ` with `Nat.Prime (f i) ∧ f i ∣ n + i`. The only addition is the hypothesis `n + m ≤ 400`. The statement is not vacuous: for example $n=24,m=4$ (the run $24,\dots,28$) satisfies all hypotheses.
--
--   **Why this is a variation.** This is a variation of the open platform problem grimm_conjecture (Grimm's conjecture on distinct prime divisors of composite runs). It is the first explicit finite range, every run of composites below 400, in the parent's own formulation. It is a partial result that supplies the matching (Hall-type) base cases from which a general argument or a stronger verified range has to start.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   C. A. Grimm, A conjecture on consecutive composite numbers, Amer. Math. Monthly 76 (1969), 1126-1128 (cited from memory, not re-checked); Erdos and Selfridge, Some problems on the prime factors of consecutive integers II (1971), relate it to prime gaps (cited from memory). The range n + m <= 400 was checked directly in Python by bipartite matching. It is the platform theorem grimm_conjecture with the extra hypothesis n + m <= 400.

import Mathlib

set_option autoImplicit false

namespace LefebvreVariations
theorem grimm_conjecture_of_add_le_400 (n m : ℕ) (hn : 2 ≤ n)
    (hm : 1 ≤ m) (hle : n + m ≤ 400)
    (hcomp : ∀ k, n ≤ k → k ≤ n + m → ¬Nat.Prime k) :
    ∃ f : Fin (m + 1) → ℕ,
      Function.Injective f ∧
      ∀ i, Nat.Prime (f i) ∧ f i ∣ (n + i) := by sorry
end LefebvreVariations
