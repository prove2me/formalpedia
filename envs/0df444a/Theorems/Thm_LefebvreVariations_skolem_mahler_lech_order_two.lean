-- Prove2me | Theorems.Thm_LefebvreVariations_skolem_mahler_lech_order_two
-- name    : LefebvreVariations.skolem_mahler_lech_order_two
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-25T23:49:14.471806+00:00
-- url     : https://prove2.me/theorems/82da698a-1905-49e8-bd11-a68ca91ca164
-- title:
--   Lefebvre's variations, No. 62 — on a theme by Skolem-Mahler-Lech: the Skolem–Mahler–Lech theorem for recurrences of order two
-- statement:
--   Let $K$ be a field of characteristic $0$, let $c_0,c_1\in K$ and let $(u_n)_{n\ge 0}$ satisfy
--   $$
--   u_{n+2}=c_0\,u_n+c_1\,u_{n+1}\qquad(n\ge 0).
--   $$
--   If $u_n=0$ for infinitely many $n$, then there are $a\ge 0$ and $d\ge 1$ with
--   $$
--   u_{a+dt}=0\qquad\text{for all } t\ge 0 .
--   $$
--   In words: the zeros of an order-two linear recurrence with infinitely many zeros contain a full arithmetic progression.
--
--   This is the Skolem–Mahler–Lech theorem in its first non-trivial order. For order two it is a divisibility property of Lucas sequences: a zero at $m$ and another at $m+r$ forces zeros at every $m+rk$.
--
--   **Formalization Note** The recurrence is Mathlib's `LinearRecurrence K` with `E.order = 2`, so `E.IsSolution u` says `u (n + 2) = c₀ u n + c₁ u (n + 1)` for all `n`, where $c_0,c_1$ may be zero. The conclusion asks for `a d : ℕ` with `0 < d`.
--
--   **Why this is a variation.** This is a variation on the open platform problem EvasivePatterns.skolem_mahler_lech (the Skolem-Mahler-Lech theorem for arbitrary linear recurrences over a field of characteristic zero). It restricts to recurrences of order exactly two, the first non-trivial order, where the zero set is controlled by a divisibility argument on Lucas sequences. The general theorem, including every order of at least three, remains open on the platform.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   C. Lech, A note on recurring series, Ark. Mat. 2 (1953), 417-421 (the general theorem; cited from memory, page numbers not verified). The order-two case is the classical divisibility property of Lucas sequences, going back to E. Lucas (1878) (cited from memory); it is an elementary consequence of the definitions of a second-order recurrence. Parent on the platform: EvasivePatterns.skolem_mahler_lech, which cites Lech 1953 as used in Faro-Marino-Pavone, A Complete Characterization of Eventually Evasive Binary Patterns, section 6.

import Mathlib

namespace LefebvreVariations

/-- The Skolem–Mahler–Lech theorem (Evasive Patterns §6, citing Lech 1953) at its first
non-trivial order: a linear recurrence of order `2` over a field of characteristic zero
with infinitely many zeros vanishes along an infinite arithmetic progression.
Source: C. Lech, *A note on recurring series*, Ark. Mat. 2 (1953), 417–421 (general
case); the order-two case is the classical divisibility property of Lucas sequences
(cited from memory, not checked against a specific page).

**Formalization Note** A recurrence is Mathlib's `LinearRecurrence K`, whose `order` is
the number of coefficients, so `E.order = 2` means `u (n + 2) = c₀ u n + c₁ u (n + 1)`
for all `n`, with `c₀`, `c₁` arbitrary (possibly zero). An infinite arithmetic progression
is `{a + d t : t ∈ ℕ}` with `d > 0`. -/
theorem skolem_mahler_lech_order_two {K : Type*} [Field K] [CharZero K]
    (E : LinearRecurrence K) (hE : E.order = 2)
    (u : ℕ → K) (hu : E.IsSolution u) (hinf : {n : ℕ | u n = 0}.Infinite) :
    ∃ a d : ℕ, 0 < d ∧ ∀ t : ℕ, u (a + d * t) = 0 := by
  sorry

end LefebvreVariations
