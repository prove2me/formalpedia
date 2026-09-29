-- Prove2me | Theorems.Thm_KontsevichHMS_isect_finite_card
-- name    : KontsevichHMS.isect_finite_card
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-15T02:51:37.718651+00:00
-- url     : https://prove2.me/theorems/79522c41-1076-4137-b32b-0524c849f59d
-- title:
--   Two transverse branes meet in $|\det(v_1,v_2)|$ points
-- statement:
--   Two closed geodesics on the flat torus $\mathbb{R}^2/\mathbb{Z}^2$ with primitive integral directions $v_1$ and $v_2$ that are not parallel meet in exactly $|\det(v_1,v_2)|$ points. This is the finiteness underlying Fukaya's definition of the morphism space of two transverse Lagrangians as the vector space spanned by their intersection points, and it gives the dimension of the Floer space $\mathrm{Hom}(b_1,b_2)$; on the mirror side it matches the dimension of the corresponding $\mathrm{Ext}$-group between the mirror sheaves.
-- source:
--   M. Kontsevich, Homological algebra of mirror symmetry, Proc. ICM Zurich 1994, arXiv:alg-geom/9411018, pp. 16 and 19 (Floer complexes are spanned by intersection points)

import Mathlib
import Definitions.Def_KontsevichHMS_TorusBrane

namespace KontsevichHMS

open Brane

/-- Two transverse branes meet in finitely many points, `|det(v₁, v₂)|` of them. -/
theorem isect_finite_card (b₁ b₂ : Brane) (h : Transverse b₁ b₂) :
    ∃ hfin : (isect b₁ b₂).Finite,
      hfin.toFinset.card = (b₁.dir.1 * b₂.dir.2 - b₁.dir.2 * b₂.dir.1).natAbs := by sorry

end KontsevichHMS
