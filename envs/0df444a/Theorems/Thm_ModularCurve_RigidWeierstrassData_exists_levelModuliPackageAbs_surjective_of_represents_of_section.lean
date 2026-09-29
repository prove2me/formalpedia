-- Prove2me | Theorems.Thm_ModularCurve_RigidWeierstrassData_exists_levelModuliPackageAbs_surjective_of_represents_of_section
-- name    : ModularCurve.RigidWeierstrassData.exists_levelModuliPackageAbs_surjective_of_represents_of_section
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.379182+00:00
-- url     : https://prove2.me/theorems/df53e087-dfc9-5bc9-b2e8-76bc455d7e10
-- title:
--   Representability via a normal-form section, with surjection onto B₀
-- statement:
--   Let $A$ be a commutative ring and let $R$ be a rigid Weierstrass datum over $A$: a functor $T \mapsto R.\mathrm{Raw}\,T$ on $A$-algebras, with functorial maps `R.mapRing`, a Weierstrass curve `R.curve x` over $T$ attached to each $x$ with unit discriminant and compatible with base change, and an action `R.act` of the group `WeierstrassCurve.VariableChange T` on $R.\mathrm{Raw}\,T$ inducing the usual action on curves and commuting with base change. Let $C$ be an $A$-algebra and $x_u : R.\mathrm{Raw}\,C$ be such that for every $A$-algebra $T$ and every $x : R.\mathrm{Raw}\,T$ there is a unique $A$-algebra map $\psi : C \to T$ with $R.\mathrm{mapRing}\,\psi\,x_u = x$; thus $C$ represents $R.\mathrm{Raw}$ with universal object $x_u$. Assume further that the action is free: if `R.act C x = x` then $C = 1$. Finally, let $NF$ be a predicate on $R.\mathrm{Raw}\,T$ for each $A$-algebra $T$, stable under base change along any $A$-algebra map, and such that for every $x$ there is exactly one variable change $C$ with $NF(R.\mathrm{act}\,C\,x)$. Then there exist a moduli package $P$ for `R.toLevelModuliDatum` — an $A$-algebra $B_0$ together with a point $\mathrm{univ}$ of the quotient functor $T \mapsto R.\mathrm{Pt}\,T$ (orbits of $R.\mathrm{Raw}\,T$ under variable changes, with $j$-invariant function given by `jOfUnit`) such that for every $A$-algebra $T$ every point of $R.\mathrm{Pt}\,T$ is $\mathrm{map}\,\varphi\,\mathrm{univ}$ for a unique $A$-algebra map $\varphi : B_0 \to T$ — and a surjective $A$-algebra map $\pi : C \to B_0$.
--
--   This is the abstract "quotient by the variable changes, using a normal-form section" step in the construction of moduli rings for elliptic curves with level structure, in the functorial language of Katz–Mazur: a representable functor of Weierstrass data with a normal form descends to a representable functor of isomorphism classes. The surjection $\pi : C \to B_0$ is what the applications need, since it transports finiteness and finite-type properties from the representing algebra of the rigid data to the moduli ring; it is invoked in the constructions of moduli packages for full level and $\Gamma_0$-type data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_RigidWeierstrassData_exists_levelModuliPackageAbs_surjective_of_represents_of_section.lean

import Mathlib
import Definitions.Def_ModularCurve_LevelModuliPackage
import Definitions.Def_ModularCurve_LevelModuliPackageAbs
import Definitions.Def_ModularCurve_WeierstrassLevelModuliDatum

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open ModularCurve

theorem ModularCurve.RigidWeierstrassData.exists_levelModuliPackageAbs_surjective_of_represents_of_section
    {A : Type u} [CommRing A] (R : RigidWeierstrassData.{u} A)

    (C : Type u) [CommRing C] [Algebra A C] (xᵤ : R.Raw C)
    (hrep : ∀ (T : Type u) [CommRing T] [Algebra A T] (x : R.Raw T),
        ∃! ψ : C →ₐ[A] T, R.mapRing ψ xᵤ = x)

    (hrigid : ∀ (T : Type u) [CommRing T] [Algebra A T] (x : R.Raw T) (C : WeierstrassCurve.VariableChange T),
      R.act C x = x → C = 1)

    (NF : ∀ (T : Type u) [CommRing T] [Algebra A T], R.Raw T → Prop)
    (hNF_map : ∀ (T T' : Type u) [CommRing T] [Algebra A T] [CommRing T'] [Algebra A T'] (f : T →ₐ[A] T')
      (x : R.Raw T), NF T x → NF T' (R.mapRing f x))
    (hNF_sec : ∀ (T : Type u) [CommRing T] [Algebra A T] (x : R.Raw T),
      ∃! C : WeierstrassCurve.VariableChange T, NF T (R.act C x)) :
    ∃ (P : LevelModuliPackageAbs A R.toLevelModuliDatum) (π : C →ₐ[A] P.B₀), Function.Surjective π := by sorry
