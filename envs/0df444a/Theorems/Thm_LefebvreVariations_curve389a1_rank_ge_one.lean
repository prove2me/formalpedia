-- Prove2me | Theorems.Thm_LefebvreVariations_curve389a1_rank_ge_one
-- name    : LefebvreVariations.curve389a1_rank_ge_one
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-26T21:37:32.203773+00:00
-- url     : https://prove2.me/theorems/9c005c15-b3d1-5553-ad72-c67444df53b4
-- title:
--   Lefebvre's variations, No. 235 — on a theme by Birch and Swinnerton-Dyer: the elliptic curve 389a1 has rank at least 1
-- statement:
--   Let $E$ be the elliptic curve $389a1$ over $\mathbb{Q}$ given by the Weierstrass equation
--   $$y^2+y=x^3+x^2-2x ,$$
--   that is $[a_1,a_2,a_3,a_4,a_6]=[0,1,1,-2,0]$ (discriminant $389$). Then the group of rational points $E(\mathbb{Q})$ has rank at least $1$:
--   $$\operatorname{rank}_{\mathbb{Z}}E(\mathbb{Q})\ \ge\ 1 .$$
--
--   The point $P=(0,0)$ lies on $E$ and has infinite order (its multiples $nP$ never return to the point at infinity; by Mazur's theorem a torsion point has order at most $12$). The curve $389a1$ is the elliptic curve of smallest conductor with rank $2$; $(1,0)$ and $(-1,1)$ also lie on it.
--
--   **Formalization Note** The curve is `(⟨0, 1, 1, -2, 0⟩ : WeierstrassCurve ℚ)` (coefficients `a₁ a₂ a₃ a₄ a₆`), `toAffine.Point` is Mathlib's group of rational points including the point at infinity, and `Module.finrank ℤ` is the rank of that abelian group as a `ℤ`-module (if the group were not finitely generated, `finrank` would be `0`, so `1 ≤ finrank` is a genuine statement).
--
--   **Why this is a variation.** First step of the open platform problem Rank2Sha.curve389a1_rank_ge_two (the curve 389a1 has rank at least 2): rank at least 1, witnessed by the non-torsion point (0,0). The curve is written with explicit Weierstrass coefficients [0,1,1,-2,0], which are the coefficients of the platform curve389a1 (parent read-back: quintuple (0,1,1,-2,0)); not imported as a formal consequence, but the same curve.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   Parent: Rank2Sha.curve389a1_rank_ge_two (open on the platform: 2 <= Module.finrank ℤ curve389a1.Point); this is the weaker statement rank >= 1 for the same curve, stated with the explicit coefficients [0,1,1,-2,0] of the Cremona label 389a1 (not importing the platform definition). The platform read-back of the parent confirms that curve389a1 is the quintuple (0,1,1,-2,0), so the statement is the first half of the parent. Rank 2 is the LMFDB value cited by the parent.
--   Source: J. Cremona, 'Algorithms for Modular Elliptic Curves', tables: 389a1 = [0,1,1,-2,0], rank 2 (cited from memory). Checked here in Python: discriminant 389; (0,0) and (-1,1) lie on the curve; the multiples nP for n = 1..14 of (0,0), computed in exact rational arithmetic, never reach the point at infinity, so (0,0) is non-torsion by Mazur's bound (cited from memory).

import Mathlib

set_option autoImplicit false

namespace LefebvreVariations

/-- The elliptic curve `389a1 : y² + y = x³ + x² − 2x` over `ℚ` has positive rank: the point `(0, 0)`
has infinite order. This is the first step of `Rank2Sha.curve389a1_rank_ge_two` (rank at least 2,
second generator `(-1, 1)`). -/
theorem curve389a1_rank_ge_one :
    1 ≤ Module.finrank ℤ ((⟨0, 1, 1, -2, 0⟩ : WeierstrassCurve ℚ).toAffine.Point) := by
  sorry

end LefebvreVariations
