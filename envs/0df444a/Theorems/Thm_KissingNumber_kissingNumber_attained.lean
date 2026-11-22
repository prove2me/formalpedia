-- Prove2me | Theorems.Thm_KissingNumber_kissingNumber_attained
-- name    : KissingNumber.kissingNumber_attained
-- status  : Open
-- author  : @LG
-- created : 2026-11-21T21:56:05.457575+00:00
-- url     : https://prove2.me/theorems/2824286d-be46-4260-925f-110d2f780e04
-- title:
--   Well-posedness: the kissing number is an attained finite maximum
-- statement:
--   For every dimension $d$, the supremum defining the kissing number is a finite maximum that is actually attained: there exists a kissing configuration $C$ in $\mathbb{R}^d$ whose cardinality equals $\tau(d)$,
--   $$\exists\,C,\quad |C|=\tau(d).$$
--   In particular $\tau(d)$ is finite (never $\infty$). This is the well-posedness of the kissing number problem: the maximum exists because the achievable cardinalities form a bounded, non-empty set of natural numbers (a crude volume bound gives $\tau(d)\le 3^d$).
--
--   This milestone turns the `ℕ∞`-valued supremum into an honest natural-number maximum, which every exact-value theorem implicitly relies on.
--
--   **Formalization Note.** The witness is a `KissingConfig d`; the equality is in `ℕ∞`, and finiteness follows because the right-hand side is a finite cardinal.
-- source:
--   https://en.wikipedia.org/wiki/Kissing_number (Rough volume estimates); standard packing/volume argument, Conway & Sloane, Sphere Packings, Lattices and Groups, 3rd ed., Ch. 2

import Definitions.Def_KissingNumber

namespace KissingNumber
theorem kissingNumber_attained (d : ℕ) : ∃ C : KissingConfig d, (C.points.card : ℕ∞) = kissingNumber d := by sorry
end KissingNumber
