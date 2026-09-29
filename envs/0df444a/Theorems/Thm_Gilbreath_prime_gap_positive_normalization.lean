-- Prove2me | Theorems.Thm_Gilbreath_prime_gap_positive_normalization
-- name    : Gilbreath.prime_gap_positive_normalization
-- status  : Proved
-- author  : @EvanLLL
-- created : 2026-09-25T14:07:27.733227+00:00
-- url     : https://prove2.me/theorems/1ec7a8a2-3f55-409c-9dcd-eff7fb3cb3fe
-- title:
--   Unique positive normalization of the prime-gap tail
-- statement:
--   Let $p_0=2<p_1=3<p_2=5<\cdots$ be the increasing sequence of primes and let $d^1(n)=|p_{n+1}-p_n|$ be the first difference row.
--
--   There is a unique sequence $b:\mathbb N\to\mathbb N$ satisfying
--   $$
--   d^1(n+1)=2b_n,\qquad b_n\ge1\quad(n\ge0).
--   $$
--
--   Thus the tail beginning with the gap $p_2-p_1$ has a canonical positive integral normalization. This identifies the input sequence for the binary reformulation of the Gilbreath triangle and removes an arbitrary choice of a halved gap sequence. The first gap $p_1-p_0=1$ is deliberately excluded.
-- source:
--   Derived normalization lemma for the defining first row in Definitions.Def_gilbreath_triangle, https://prove2.me/theorems/54d54393-a9a5-4c00-b9f5-108b4f94026c, formula d^1(n)=|p_(n+1)-p_n|. Uses that all primes after 2 are odd and the prime enumeration is strictly increasing. This elementary consequence is formalized here; it is not a claim that the open Gilbreath conjecture is proved.

import Definitions.Def_gilbreath_triangle

namespace Gilbreath
theorem prime_gap_positive_normalization :
    ∃! b : ℕ → ℕ, (∀ n, d 1 (n + 1) = 2 * b n) ∧ (∀ n, 1 ≤ b n) := by sorry
end Gilbreath
