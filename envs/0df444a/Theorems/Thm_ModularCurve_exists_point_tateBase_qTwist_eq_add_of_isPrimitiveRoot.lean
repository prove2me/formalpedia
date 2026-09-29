-- Prove2me | Theorems.Thm_ModularCurve_exists_point_tateBase_qTwist_eq_add_of_isPrimitiveRoot
-- name    : ModularCurve.exists_point_tateBase_qTwist_eq_add_of_isPrimitiveRoot
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:51.361078+00:00
-- url     : https://prove2.me/theorems/6c6a4627-4553-50c6-a5c6-883f7baee2f0
-- title:
--   M-torsion of Tate(q^M) and the inertia transvection
-- statement:
--   Let $K$ be a field, let $M$ be a nonzero natural number with $2 \le M$, and let $\zeta$ be a unit of $K$ whose underlying element is a primitive $M$-th root of unity. Work over the field of formal Laurent series $K((q))$, i.e. `LaurentSeries K`, and let `tateBase K M` be the Weierstrass curve obtained from the universal Tate curve with coefficients in $K((q))$ by the substitution $q \mapsto q^M$ (the ring endomorphism `qExpand` multiplying all exponents by $M$), so `tateBase K M` is $\mathrm{Tate}(q^M)$. Let `qTwist ζ` be the ring endomorphism of $K((q))$ multiplying the coefficient of $q^k$ by $\zeta^k$, i.e. the substitution $q \mapsto \zeta q$. The assertion is that there exist Laurent series $x_A, y_A, x_B, y_B$ together with nonsingularity witnesses for $(x_A,y_A)$, for $(x_B,y_B)$ and for $(\mathrm{qTwist}\,\zeta\,x_B, \mathrm{qTwist}\,\zeta\,y_B)$ on the affine model of `tateBase K M`, such that, writing $A$ and $B$ for the corresponding points of the group of points: $M \cdot A = 0$ and $M \cdot B = 0$; for all integers $a,b$, the relation $a \cdot A + b \cdot B = 0$ forces $M \mid a$ and $M \mid b$; $\mathrm{qTwist}\,\zeta$ fixes both $x_A$ and $y_A$; and the point with coordinates $(\mathrm{qTwist}\,\zeta\,x_B, \mathrm{qTwist}\,\zeta\,y_B)$ equals $A + B$.
--
--   This is the Tate-curve computation of the action of the cusp (tame) inertia $q \mapsto \zeta q$ of $K((q))$ over $K((q^M))$ on a pair of independent $M$-torsion points of $\mathrm{Tate}(q^M)$, classically the images of the parameters $u = \zeta$ and $u = q$ under Tate's uniformisation, the action being through the transvection $\begin{pmatrix} 1 & 1 \\ 0 & 1 \end{pmatrix}$. It is the local input at $j = \infty$ used by [`WeierstrassCurve.exists_algEquiv_map_eq_smul_and_map_eq_smul_add_of_transcendental_j`](thm.html#WeierstrassCurve.exists_algEquiv_map_eq_smul_and_map_eq_smul_add_of_transcendental_j) for the monodromy on the $M$-torsion of an elliptic curve with transcendental $j$-invariant.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_point_tateBase_qTwist_eq_add_of_isPrimitiveRoot.lean

import Mathlib
import Definitions.Def_ModularCurve_TateSlots
import Definitions.Def_ModularCurve_PhiGen

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve WeierstrassCurve WeierstrassCurve.Affine

universe u in

theorem ModularCurve.exists_point_tateBase_qTwist_eq_add_of_isPrimitiveRoot
    (K : Type u) [Field K] [DecidableEq (LaurentSeries K)] (M : ℕ) [NeZero M] (hM : 2 ≤ M)
    (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) M) :
    ∃ (xA yA xB yB : LaurentSeries K)
      (hA : (tateBase K M).toAffine.Nonsingular xA yA)
      (hB : (tateBase K M).toAffine.Nonsingular xB yB)
      (hB' : (tateBase K M).toAffine.Nonsingular (qTwist ζ xB) (qTwist ζ yB)),
      M • (Point.some xA yA hA) = 0 ∧ M • (Point.some xB yB hB) = 0 ∧
      (∀ a b : ℤ, a • Point.some xA yA hA + b • Point.some xB yB hB = 0 →
        (M : ℤ) ∣ a ∧ (M : ℤ) ∣ b) ∧
      qTwist ζ xA = xA ∧ qTwist ζ yA = yA ∧
      Point.some (qTwist ζ xB) (qTwist ζ yB) hB' = Point.some xA yA hA + Point.some xB yB hB := by sorry
