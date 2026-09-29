-- Prove2me | Theorems.Thm_ModularCurve_LevelModuliPackageAbs_natCard_algHom_apply_jOf_univ_eq_natCard_pt_jOf_eq
-- name    : ModularCurve.LevelModuliPackageAbs.natCard_algHom_apply_jOf_univ_eq_natCard_pt_jOf_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:42.499921+00:00
-- url     : https://prove2.me/theorems/b2d6dfaf-50af-5fc4-af95-2bbb542514b0
-- title:
--   Fibres of j on a representing object count moduli points
-- statement:
--   Let $A$ be a commutative ring and let $D$ be a level moduli datum over $A$: a functorial assignment $T \mapsto D.\mathrm{Pt}(T)$ of a type of points to each commutative $A$-algebra $T$, together with a transport operation $D.\mathrm{map}$ along $A$-algebra maps satisfying the identity and composition laws, and a $j$-invariant $D.\mathrm{jOf} : D.\mathrm{Pt}(T) \to T$ compatible with transport, in the sense that $D.\mathrm{jOf}(D.\mathrm{map}\,f\,x) = f(D.\mathrm{jOf}\,x)$. Let $P_0$ be an abstract representing object for $D$: a commutative $A$-algebra $B_0 = P_0.B_0$ together with a point $\mathrm{univ} \in D.\mathrm{Pt}(B_0)$ such that for every commutative $A$-algebra $T$ and every $x \in D.\mathrm{Pt}(T)$ there is a unique $A$-algebra map $\varphi : B_0 \to T$ with $D.\mathrm{map}\,\varphi\,\mathrm{univ} = x$. Let $T$ be a commutative $A$-algebra and $t \in T$. The assertion is the equality of natural cardinalities $$\#\{\varphi : B_0 \to_A T : \varphi(D.\mathrm{jOf}\,\mathrm{univ}) = t\} = \#\{x \in D.\mathrm{Pt}(T) : D.\mathrm{jOf}\,x = t\},$$ both cardinalities being taken in the sense of `Nat.card`, so that both sides are $0$ when the sets concerned are infinite.
--
--   This is the elementary bookkeeping step which transfers a count of points of a moduli problem with prescribed $j$-invariant into a count of $A$-algebra homomorphisms out of the representing object sending the universal $j$-invariant to the prescribed value. It is used in the computation of the number of $A$-algebra maps from the full-level ring into a field over a transcendental $j$, both in the $\Gamma_0$ and in the Diamond variants.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_LevelModuliPackageAbs_natCard_algHom_apply_jOf_univ_eq_natCard_pt_jOf_eq.lean

import Mathlib
import Definitions.Def_ModularCurve_LevelModuliPackage
import Definitions.Def_ModularCurve_LevelModuliPackageAbs

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open ModularCurve

theorem ModularCurve.LevelModuliPackageAbs.natCard_algHom_apply_jOf_univ_eq_natCard_pt_jOf_eq
    {A : Type u} [CommRing A] {D : LevelModuliDatum.{u} A} (P₀ : LevelModuliPackageAbs A D)
    (T : Type u) [CommRing T] [Algebra A T] (t : T) :
    Nat.card {φ : P₀.B₀ →ₐ[A] T // φ (D.jOf P₀.univ) = t} = Nat.card {x : D.Pt T // D.jOf x = t} := by sorry
