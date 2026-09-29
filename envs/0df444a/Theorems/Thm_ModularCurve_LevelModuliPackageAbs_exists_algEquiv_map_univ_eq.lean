-- Prove2me | Theorems.Thm_ModularCurve_LevelModuliPackageAbs_exists_algEquiv_map_univ_eq
-- name    : ModularCurve.LevelModuliPackageAbs.exists_algEquiv_map_univ_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:41.339792+00:00
-- url     : https://prove2.me/theorems/70bf958c-32d4-5537-8292-f821918d7fd2
-- title:
--   Uniqueness of an abstract representing package of a level-moduli datum
-- statement:
--   Fix a commutative ring $A$ and a level-moduli datum $D$ over $A$, that is: an assignment $T \mapsto D.\mathrm{Pt}\,T$ of a type to each commutative $A$-algebra $T$ (all types in a single universe), a pushforward $D.\mathrm{map}\,f : D.\mathrm{Pt}\,T \to D.\mathrm{Pt}\,T'$ along each $A$-algebra map $f : T \to T'$ which is functorial (the identity map acts as the identity, and $D.\mathrm{map}\,(g \circ f) = D.\mathrm{map}\,g \circ D.\mathrm{map}\,f$), together with a function $D.\mathrm{jOf} : D.\mathrm{Pt}\,T \to T$ satisfying $D.\mathrm{jOf}(D.\mathrm{map}\,f\,x) = f(D.\mathrm{jOf}\,x)$. Let $P$ and $P'$ be two abstract representing packages for $D$: each consists of a commutative $A$-algebra $B_0$ together with a point $\mathrm{univ} \in D.\mathrm{Pt}\,B_0$ such that for every commutative $A$-algebra $T$ and every $x \in D.\mathrm{Pt}\,T$ there is exactly one $A$-algebra homomorphism $\varphi : B_0 \to T$ with $D.\mathrm{map}\,\varphi\,(\mathrm{univ}) = x$. The conclusion asserts the existence of an $A$-algebra isomorphism $e : P.B_0 \xrightarrow{\sim} P'.B_0$ whose underlying $A$-algebra homomorphism carries the universal point of $P$ to that of $P'$, i.e. $D.\mathrm{map}\,e\,(P.\mathrm{univ}) = P'.\mathrm{univ}$.
--
--   This is the Yoneda-style uniqueness statement for a representing object of a moduli functor with $j$-invariant: a representing pair $(B_0,\mathrm{univ})$ is unique up to a unique $A$-algebra isomorphism matching universal points. It is used throughout the treatment of moduli of elliptic curves with level structure to transport properties (flatness, reducedness of fibres, explicit chart computations) between a package constructed by hand and a package obtained by base change.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_LevelModuliPackageAbs_exists_algEquiv_map_univ_eq.lean

import Mathlib
import Definitions.Def_ModularCurve_LevelModuliPackage
import Definitions.Def_ModularCurve_LevelModuliPackageAbs

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open ModularCurve

theorem ModularCurve.LevelModuliPackageAbs.exists_algEquiv_map_univ_eq
    {A : Type u} [CommRing A] {D : LevelModuliDatum.{u} A} (P P' : LevelModuliPackageAbs A D) :
    ∃ e : P.B₀ ≃ₐ[A] P'.B₀, D.map (e : P.B₀ →ₐ[A] P'.B₀) P.univ = P'.univ := by sorry
