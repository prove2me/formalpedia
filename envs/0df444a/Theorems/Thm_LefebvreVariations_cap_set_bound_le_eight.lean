-- Prove2me | Theorems.Thm_LefebvreVariations_cap_set_bound_le_eight
-- name    : LefebvreVariations.cap_set_bound_le_eight
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-25T23:42:32.462602+00:00
-- url     : https://prove2.me/theorems/bdaa5feb-7fab-5770-b922-10a58c368a19
-- title:
--   Lefebvre's variations, No. 50 — on a theme by Ellenberg and Gijswijt: cap sets in F_3^n have at most 2.756^n points for n at most 8
-- statement:
--   Let $n$ be an integer with $1\le n\le 8$, and let $A\subseteq\mathbb{F}_3^{\,n}$ be a cap set, that is, a set containing no three distinct points whose sum is $0$ (equivalently, no non-trivial $3$-term arithmetic progression $x,\,x+d,\,x+2d$ with $d\neq 0$). Then
--   $$
--   |A| \;\le\; 2.756^{\,n}.
--   $$
--
--   This is the range $1\le n\le 8$ of the Ellenberg–Gijswijt cap set bound, which says that cap sets in $\mathbb{F}_3^{\,n}$ have size $O(2.756^{\,n})$ (after Croot–Lev–Pach). The full inequality $|A|\le 2.756^{\,n}$ for every $n\ge 1$ is an open problem on the platform in this exact form; for small $n$ the classical line-counting bound $|A|\le (3^n+1)/2$ is already below $2.756^{\,n}$, and it stops being so at $n=9$.
--
--   **Formalization Note** The set $A$ is a `Finset (Fin n → ZMod 3)` and the cap condition is `∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A, x + y + z = 0 → x = y`. Over $\mathbb{F}_3$ the relation $x+y+z=0$ with $x=y$ forces $z=x$, so this says exactly that no three distinct points of $A$ sum to $0$ (the three points of a line); the empty set and single points are allowed. The conclusion is the real inequality `(A.card : ℝ) ≤ 2.756 ^ n` with the decimal literal $2.756 = 2756/1000$ exactly, and $n$ ranges over $1\le n\le 8$ (both bounds inclusive).
--
--   **Why this is a variation.** Variation on the open theorem cap_set_bound (a cap set in $\mathbb F_3^n$ has size at most $2.756^n$, Ellenberg–Gijswijt). It keeps the parent's statement unchanged and adds the hypothesis $n\le8$: a finite range of small dimensions where the bound can be attacked by explicit counting and classification of small cap sets, so it is a partial result of the parent rather than a restatement; settling it checks the constant $2.756$ at the sizes where cap sets are best understood.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   J. S. Ellenberg and D. Gijswijt, On large subsets of F_q^n with no three-term arithmetic progression, Annals of Mathematics 185 (2017), 339-343 (after E. Croot, V. F. Lev and P. P. Pach, Progression-free sets in Z_4^n are exponentially small, Annals of Mathematics 185 (2017), 331-337); journal volume and page numbers cited from memory, not re-checked. The line-counting bound |A| <= (3^n+1)/2 for a cap set in F_3^n is folklore (elementary: through a point of the cap, each of the (3^n-1)/2 lines through it contains at most one other point of the cap); no source is claimed for it. Origin of this statement: the range 1 <= n <= 8 of the platform theorem cap_set_bound (Open), whose conclusion and hypotheses it copies verbatim, with the extra hypothesis n <= 8; it is proved by the line-counting bound together with the arithmetic check that (3^n+1)/2 <= 2.756^n for n <= 8 (3281 <= 3328.4 at n = 8, while 9842 > 9173.0 at n = 9).

import Mathlib

namespace LefebvreVariations

/-- The cap set bound `|A| ≤ 2.756^n` (Ellenberg–Gijswijt) in the range `1 ≤ n ≤ 8`, where it
already follows from the elementary line-counting bound `|A| ≤ (3^n + 1)/2`: through a point
`x` of a cap, each of the `(3^n - 1)/2` lines through `x` carries at most one further point
of the cap. The elementary bound is below `2.756^n` exactly for `n ≤ 8`
(`3281 ≤ 3328.38…` at `n = 8`, `9842 > 9173.03…` at `n = 9`).
Source: the cap set bound is Ellenberg and Gijswijt, "On large subsets of `F_q^n` with no three-term
arithmetic progression", Annals of Math. 185 (2017), 339-343 (after Croot–Lev–Pach); the
line-counting bound is folklore (cited from memory). -/
theorem cap_set_bound_le_eight (n : ℕ) (hn : 1 ≤ n) (hn8 : n ≤ 8)
    (A : Finset (Fin n → ZMod 3))
    (hcap : ∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A, x + y + z = 0 → x = y) :
    (A.card : ℝ) ≤ 2.756 ^ n := by
  sorry

end LefebvreVariations
