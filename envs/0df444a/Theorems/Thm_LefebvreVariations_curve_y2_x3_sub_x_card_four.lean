-- Prove2me | Theorems.Thm_LefebvreVariations_curve_y2_x3_sub_x_card_four
-- name    : LefebvreVariations.curve_y2_x3_sub_x_card_four
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-26T21:37:51.94035+00:00
-- url     : https://prove2.me/theorems/63cf49c2-fb1f-4c6d-978c-d6b1c1ca81ca
-- title:
--   Lefebvre's variations, No. 198 — on a theme by Mordell: the elliptic curve y^2 = x^3 - x over the rationals has exactly 4 points
-- statement:
--   Let $E$ be the elliptic curve over $\mathbb{Q}$ given by
--   $$y^2=x^3-x .$$
--   Then $E(\mathbb{Q})$ is finite and has exactly four elements, the point at infinity and $(0,0)$, $(1,0)$, $(-1,0)$:
--   $$|E(\mathbb{Q})|=4,\qquad E(\mathbb{Q})\cong\mathbb{Z}/2\times\mathbb{Z}/2 .$$
--
--   This is equivalent to Fermat's theorem that no right triangle with rational sides has area $1$ (the number $1$ is not congruent), and is the standard first example of a Mordell–Weil group computed by descent: the curve has rank $0$ and torsion subgroup $\mathbb{Z}/2\times\mathbb{Z}/2$.
--
--   **Formalization Note** The curve is `(⟨0, 0, 0, -1, 0⟩ : WeierstrassCurve ℚ)` (so `a₄ = -1`, all other coefficients `0`), and `toAffine.Point` is Mathlib's type of rational points including the point at infinity `0`. `Nat.card` is the cardinality of that type; it equals `0` for an infinite type, so the equality `= 4` forces finiteness.
--
--   **Why this is a variation.** Computed instance of the open platform problem BSD.mordell (E(Q) is finitely generated): for y^2 = x^3 - x the group E(Q) is Z/2 x Z/2 of order 4 (Fermat's descent, equivalent to 1 not being a congruent number). Nat.card = 4 for this one curve implies the parent's Module.Finite conclusion for it, so it is a special case with a stronger conclusion.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   Parent: BSD.mordell (Mordell's theorem, E(Q) finitely generated, open on the platform for all E); the parent is stated as Module.Finite ℤ W.toAffine.Point for every elliptic W over Q. This statement gives, for the single curve W = y^2 = x^3 - x (discriminant 64, so W.IsElliptic holds), the exact group E(Q) of order 4; Nat.card = 4 implies Module.Finite for that W, so it is a special case of the parent (a stronger conclusion on one curve).
--   Source: P. de Fermat (descent), see J. Silverman, 'The Arithmetic of Elliptic Curves', Prop. X.6.2 for y^2 = x^3 - x (reference cited from memory, number not verified). Checked here: the only integer points with |x| <= 50 are (-1,0), (0,0), (1,0).

import Mathlib

set_option autoImplicit false

namespace LefebvreVariations

/-- Fermat: the elliptic curve `y² = x³ - x` over `ℚ` has exactly four rational points (including the
point at infinity): `E(ℚ) ≅ ℤ/2 × ℤ/2`. In particular `E(ℚ)` is finite, hence finitely generated, as
predicted by `BSD.mordell`. -/
theorem curve_y2_x3_sub_x_card_four :
    Nat.card ((⟨0, 0, 0, -1, 0⟩ : WeierstrassCurve ℚ).toAffine.Point) = 4 := by
  sorry

end LefebvreVariations
