-- Prove2me | Theorems.Thm_ModularCurve_ramificationIndexAlong_mul_placeWidth_eq_placeWidth_restrictAlong_of_coe_eq
-- name    : ModularCurve.ramificationIndexAlong_mul_placeWidth_eq_placeWidth_restrictAlong_of_coe_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.618386+00:00
-- url     : https://prove2.me/theorems/2f9fd14a-5c6a-5940-8054-17dc8b057b16
-- title:
--   Width transport along an embedding fixing q-expansions
-- statement:
--   Let $k$ be an algebraically closed field and let $M,M'$ be nonzero natural numbers. For a level $N$, write $F_N = k(\bar\jmath, \bar\jmath_N)$ for the intermediate field `modularFunctionFieldC k N` of $k((q))$ generated over $k$ by the $j$-series `jqModC k` and its $N$-fold $q$-expansion `jqNModC k N`, and let `jGeomGen k N` denote the element `jqModC k` of $F_N$. Let $\varphi\colon F_M \to F_{M'}$ be a $k$-algebra homomorphism whose underlying ring homomorphism is integral, and assume $\varphi$ is the identity on $q$-expansions: the Laurent series underlying $\varphi(x)$ equals that of $x$ for every $x \in F_M$. Let $p$ be a place of $F_{M'}$ over $k$, i.e. a valuation subring of $F_{M'}$, distinct from $F_{M'}$ itself, containing the image of $k$ and a principal ideal ring. Put $a = p$-evaluation of `jGeomGen k M'` (the residue of that element, pulled back to $k$, or $0$ if it is not integral at $p$), $e_j(p) = \mathrm{ord}_p(\bar\jmath - a)$ truncated to $\mathbb{N}$, and $W(a) = 3,2,1$ according as $a = 0$, $a = 1728$, or otherwise. Assume $e_j(p) \mid W(a)$. Then the ramification index of $p$ along $\varphi$, namely the least $n > 0$ with $\mathrm{ord}_p(\varphi(f)) = n$ for some nonzero $f \in F_M$, multiplied by the width $W(a)/e_j(p)$ of $p$ (natural-number division), equals the width of the restriction of $p$ along $\varphi$ (the valuation subring pulled back through $\varphi$).
--
--   This is the identity leg of the transport of place widths along a degeneracy map between modular function fields: widths are multiplied by the ramification index of the map. It is used by the corresponding statements for a degeneracy pair and for level $M s \to M$, and by the computation of $y$-depth under restriction along the tower inclusion.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_ramificationIndexAlong_mul_placeWidth_eq_placeWidth_restrictAlong_of_coe_eq.lean

import Mathlib
import Definitions.Def_ModularCurve_PlaceWidth
import Definitions.Def_AlgebraicCurve_Correspondence

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
open AlgebraicCurve ModularCurve

theorem ModularCurve.ramificationIndexAlong_mul_placeWidth_eq_placeWidth_restrictAlong_of_coe_eq
    {k : Type*} [Field k] [IsAlgClosed k] [DecidableEq k] (M M' : ℕ) [NeZero M] [NeZero M']
    (φ : ↥(modularFunctionFieldC k M) →ₐ[k] ↥(modularFunctionFieldC k M')) (hφ : φ.toRingHom.IsIntegral)
    (hcoe : ∀ x, ((φ x : ↥(modularFunctionFieldC k M')) : LaurentSeries k) = x)
    (p : Place k ↥(modularFunctionFieldC k M'))
    (hdiv : placeRamificationJ M' p ∣ jWidth (p.evalAt (jGeomGen k M'))) :
    Place.ramificationIndexAlong φ p * placeWidth M' p = placeWidth M (Place.restrictAlong φ hφ p) := by sorry
