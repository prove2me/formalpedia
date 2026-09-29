-- Prove2me | Theorems.Thm_ModularCurve_LevelModuliPackageAbs_apply_mem_range_of_map_eq_map_univ
-- name    : ModularCurve.LevelModuliPackageAbs.apply_mem_range_of_map_eq_map_univ
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:41.339792+00:00
-- url     : https://prove2.me/theorems/c25334da-bb9f-5f79-93c5-cabbbffd71a1
-- title:
--   Points lifting along ι are classified through ι
-- statement:
--   Let $A$ be a commutative ring and let $D$ be a level-moduli datum over $A$: a rule assigning to every commutative $A$-algebra $T$ a type $D.\mathrm{Pt}\,T$ of points, to every $A$-algebra map $f : T \to T'$ a map $D.\mathrm{map}\,f$ on points, functorially (identities and composites are respected), together with a $j$-invariant $D.\mathrm{jOf}$ on points compatible with $D.\mathrm{map}$. Let $P$ be an abstract representing package for $D$ over $A$: a commutative $A$-algebra $P.B_0$ with a point $P.\mathrm{univ} \in D.\mathrm{Pt}\,P.B_0$ such that for every commutative $A$-algebra $T$ and every $x \in D.\mathrm{Pt}\,T$ there is exactly one $A$-algebra homomorphism $\varphi : P.B_0 \to T$ with $D.\mathrm{map}\,\varphi\,(P.\mathrm{univ}) = x$. Let $K$ and $R_0$ be commutative $A$-algebras, let $\iota : R_0 \to K$ and $\varphi : P.B_0 \to K$ be $A$-algebra homomorphisms, and let $y \in D.\mathrm{Pt}\,R_0$ satisfy $D.\mathrm{map}\,\iota\,y = D.\mathrm{map}\,\varphi\,(P.\mathrm{univ})$. Then every value $\varphi(b)$, for $b \in P.B_0$, lies in the range of $\iota$.
--
--   This is the Yoneda-style step turning a lifting statement for points of the moduli problem into a statement about values of the classifying map: if the point cut out by $\varphi$ descends along $\iota$, then $\varphi$ itself factors through $\iota$, so $\varphi(P.B_0) \subseteq \iota(R_0)$. It is used, with $R_0$ a valuation subring or discrete valuation ring inside $K$, in the valuative criterion for the full-level moduli package (integrality of $\varphi$ on $P.B_0$ from integrality of the $j$-invariant) and in the construction of trivialising packages at full level.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_LevelModuliPackageAbs_apply_mem_range_of_map_eq_map_univ.lean

import Mathlib
import Definitions.Def_ModularCurve_LevelModuliPackage
import Definitions.Def_ModularCurve_LevelModuliPackageAbs

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open ModularCurve

theorem ModularCurve.LevelModuliPackageAbs.apply_mem_range_of_map_eq_map_univ
    {A : Type u} [CommRing A] {D : LevelModuliDatum.{u} A} (P : LevelModuliPackageAbs A D)
    (K : Type u) [CommRing K] [Algebra A K] (R₀ : Type u) [CommRing R₀] [Algebra A R₀]
    (ι : R₀ →ₐ[A] K)
    (φ : P.B₀ →ₐ[A] K) (y : D.Pt R₀) (hy : D.map ι y = D.map φ P.univ) :
    ∀ b : P.B₀, φ b ∈ Set.range ι := by sorry
