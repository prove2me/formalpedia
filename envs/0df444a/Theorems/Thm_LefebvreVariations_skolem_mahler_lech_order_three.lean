-- Prove2me | Theorems.Thm_LefebvreVariations_skolem_mahler_lech_order_three
-- name    : LefebvreVariations.skolem_mahler_lech_order_three
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-26T00:36:57.982229+00:00
-- url     : https://prove2.me/theorems/327e133f-e5b1-4023-b485-0b2fc116841f
-- title:
--   Lefebvre's variations, No. 85 — on a theme by Skolem-Mahler-Lech: the Skolem–Mahler–Lech theorem for recurrences of order three
-- statement:
--   Let $K$ be a field of characteristic $0$, let $c_0,c_1,c_2\in K$ and let $(u_n)_{n\ge 0}$ satisfy
--   $$
--   u_{n+3}=c_0\,u_n+c_1\,u_{n+1}+c_2\,u_{n+2}\qquad(n\ge 0).
--   $$
--   If $u_n=0$ for infinitely many $n$, then there are $a\ge 0$ and $d\ge 1$ with
--   $$
--   u_{a+dt}=0\qquad\text{for all } t\ge 0 .
--   $$
--
--   This is the Skolem–Mahler–Lech theorem for recurrences of order three. It is a true special case of Lech's theorem; the proof for a fixed order still uses $p$-adic analytic methods, not the elementary Lucas-sequence argument available at order two.
--
--   **Formalization Note** The recurrence is Mathlib's `LinearRecurrence K` with `E.order = 3`, so `E.IsSolution u` says `u (n + 3) = c₀ u n + c₁ u (n + 1) + c₂ u (n + 2)` for all `n`, with arbitrary (possibly zero) coefficients. The conclusion asks for `a d : ℕ` with `0 < d`.
--
--   **Why this is a variation.** This is a variation on the open platform problem EvasivePatterns.skolem_mahler_lech. It fixes the order of the recurrence at three, the first order where the elementary Lucas-sequence argument no longer applies. The statement for recurrences of arbitrary order remains open on the platform.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   C. Lech, A note on recurring series, Ark. Mat. 2 (1953), 417-421 (general theorem, of which this is the case of order three; journal, volume, pages and year confirmed in bibliographic records). Earlier cases: T. Skolem (1934) for rational recurrences and K. Mahler (1935) for algebraic ones (cited from memory). Parent on the platform: EvasivePatterns.skolem_mahler_lech, citing Lech 1953 as used in Faro-Marino-Pavone, A Complete Characterization of Eventually Evasive Binary Patterns, section 6.

import Mathlib

namespace LefebvreVariations

/-- The Skolem–Mahler–Lech theorem (Evasive Patterns §6, citing Lech 1953) for recurrences of
order `3`: a linear recurrence of order `3` over a field of characteristic zero with infinitely
many zeros vanishes along an infinite arithmetic progression.
Source: C. Lech, *A note on recurring series*, Ark. Mat. 2 (1953), 417–421 (general case,
cited from memory); the theorem for a fixed order is a special case. -/
theorem skolem_mahler_lech_order_three {K : Type*} [Field K] [CharZero K]
    (E : LinearRecurrence K) (hE : E.order = 3)
    (u : ℕ → K) (hu : E.IsSolution u) (hinf : {n : ℕ | u n = 0}.Infinite) :
    ∃ a d : ℕ, 0 < d ∧ ∀ t : ℕ, u (a + d * t) = 0 := by
  sorry

end LefebvreVariations
