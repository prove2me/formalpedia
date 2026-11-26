-- Prove2me | Theorems.Thm_LefebvreVariations_exists_isElliptic_natCard_point_eq_of_le_100
-- name    : LefebvreVariations.exists_isElliptic_natCard_point_eq_of_le_100
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-25T23:47:46.419954+00:00
-- url     : https://prove2.me/theorems/2d93b924-b083-44b7-adab-969b68564dd4
-- title:
--   Lefebvre's variations, No. 67 — on a theme by Deuring and Waterhouse: every point count in the Hasse window is attained by an elliptic curve over F_p for p at most 100
-- statement:
--   Let $p\le 100$ be a prime and let $N$ be a natural number with
--
--   $$
--   |N-(p+1)|<2\sqrt{p}.
--   $$
--
--   Then there is an elliptic curve $E$ over $\mathbb{F}_p=\mathbb{Z}/p\mathbb{Z}$, given by a Weierstrass equation $y^2+a_1xy+a_3y=x^3+a_2x^2+a_4x+a_6$ with nonzero discriminant, such that
--
--   $$
--   \#E(\mathbb{F}_p)=N .
--   $$
--
--   This is the case $p\le 100$ of the existence half of the Deuring–Waterhouse theorem: over a prime field every integer strictly inside the Hasse window $|N-(p+1)|<2\sqrt p$ is the number of points of some elliptic curve. The statement is the parent problem "Elliptic Curves with a Prescribed Point Count" restricted to the first hundred primes.
--
--   **Formalization Note.** `E : WeierstrassCurve (ZMod p)` with `E.IsElliptic`, and `Nat.card E.toAffine.Point` counts the affine points together with the point at infinity (Mathlib's `Point.zero`). The Hasse condition is written exactly as in the parent, `|(N : ℝ) - ((p : ℝ) + 1)| < 2 * Real.sqrt p`, with the added hypothesis `p ≤ 100` and `[Fact p.Prime]`. The cases `p = 2, 3` need a general Weierstrass form; the window is strict, so for example `p = 2` gives `N ∈ {1, 2, 3, 4, 5}`.
--
--   **Why this is a variation.** Variation on the open PrescribedPointCount.exists_isElliptic_natCard_point_eq (every point count in the Hasse window is attained by an elliptic curve over F_p). It restricts the parent to primes p <= 100, a finite range where explicit curves can be listed, giving a finite partial result of the parent.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   Special case p <= 100 of the existence of an elliptic curve over F_p with a prescribed number of points N in the Hasse interval |N - (p+1)| < 2 sqrt(p): M. Deuring, "Die Typen der Multiplikatorenringe elliptischer Funktionenkörper", Abh. Math. Sem. Univ. Hamburg 14 (1941) 197-272; W. C. Waterhouse, "Abelian varieties over finite fields", Ann. Sci. École Norm. Sup. (4) 2 (1969) 521-560, Theorem 4.1 (both cited from memory; the Hasse bound is the converse direction). Origin of this statement: it is the finite range p <= 100 of the open platform problem PrescribedPointCount.exists_isElliptic_natCard_point_eq (a mission by the platform's own formalisers, not the classical authors), and it is not provided there. A direct computer search found, for each of the 25 primes p <= 100 and each N in the window, an explicit curve (601 curves in all).

import Mathlib

set_option autoImplicit false

namespace LefebvreVariations

/-- **The Deuring–Waterhouse point-count theorem over `𝔽_p` for `p ≤ 100`**: for every prime
`p ≤ 100` and every `N` strictly inside the Hasse window `|N - (p + 1)| < 2√p`, some elliptic curve
over `ZMod p` has exactly `N` points (the point at infinity included). This is the case `p ≤ 100` of
Deuring, *Die Typen der Multiplikatorenringe elliptischer Funktionenkörper*, Abh. Math. Sem. Hamburg
14 (1941) 197–272, in the form of Waterhouse, *Abelian varieties over finite fields*, Ann. Sci. ÉNS
(4) 2 (1969) 521–560, Theorem 4.1 (cited from memory; Hasse's bound is the converse). -/
theorem exists_isElliptic_natCard_point_eq_of_le_100 (p : ℕ) [Fact p.Prime] (hp : p ≤ 100)
    (N : ℕ) (hN : |(N : ℝ) - ((p : ℝ) + 1)| < 2 * Real.sqrt (p : ℝ)) :
    ∃ E : WeierstrassCurve (ZMod p), E.IsElliptic ∧ Nat.card E.toAffine.Point = N := by
  sorry

end LefebvreVariations
