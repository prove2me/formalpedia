-- Prove2me | Theorems.Thm_NeronModelInfra_TopFormOrder_topFormMap_ne_zero_of_bijective_smul_of_isLocalization
-- name    : NeronModelInfra.TopFormOrder.topFormMap_ne_zero_of_bijective_smul_of_isLocalization
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.228905+00:00
-- url     : https://prove2.me/theorems/e8b703a5-adb7-5123-8a2d-1c150395f107
-- title:
--   Non-vanishing of a free top form in the differentials of a localisation
-- statement:
--   Fix a universe and let $K$ be a field, $A$ a commutative ring with a $K$-algebra structure, and $F$ a field carrying both an $A$-algebra and a $K$-algebra structure, compatibly in the sense that $K \to A \to F$ is a scalar tower. Let $M$ be a submonoid of $A$ such that $F$ is a localisation of $A$ at $M$. Let $d$ be a natural number, let $b$ be an $A$-basis of the module of Kähler differentials $\Omega_{A/K}$ indexed by $\mathrm{Fin}\,d$, and let $\omega$ be an element of the $d$-th exterior power $\bigwedge^d_A \Omega_{A/K}$ such that the map $g \mapsto g \cdot \omega$ from $A$ to $\bigwedge^d_A \Omega_{A/K}$ is bijective, i.e. $\omega$ is a free generator of that module. Then the image of $\omega$ under `TopFormOrder.topFormMap K K A F d` is non-zero in $\bigwedge^d_F \Omega_{F/K}$; here `topFormMap` is the $A$-linear map $\bigwedge^d_A \Omega_{A/K} \to \bigwedge^d_F \Omega_{F/K}$ (the target being an $A$-module by restriction of scalars along $A \to F$) corresponding, under `exteriorPower.alternatingMapLinearEquiv`, to the alternating map `ιMultiAlong K K A F d` of $d$ arguments from $\Omega_{A/K}$ to $\bigwedge^d_F \Omega_{F/K}$.
--
--   This is the statement that a generator of the line of top differential forms on a $K$-algebra with free differentials survives in the top forms of a field of fractions-type localisation of that algebra, the form-theoretic input for comparing orders of top forms. It is used in [`NeronModelInfra.exists_componentReading_data_of_smooth_of_forall_specializes`](thm.html#NeronModelInfra.exists_componentReading_data_of_smooth_of_forall_specializes).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NeronModelInfra_TopFormOrder_topFormMap_ne_zero_of_bijective_smul_of_isLocalization.lean

import Mathlib
import Definitions.Def_NeronModelInfra_TopFormOrder

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open NeronModelInfra

theorem NeronModelInfra.TopFormOrder.topFormMap_ne_zero_of_bijective_smul_of_isLocalization
    (K A F : Type u) [Field K] [CommRing A] [Algebra K A] [Field F] [Algebra A F] [Algebra K F]
    [IsScalarTower K A F] (M : Submonoid A) [IsLocalization M F]
    (d : ℕ) (b : Module.Basis (Fin d) A (Ω[A⁄K]))
    (ω : ⋀[A]^d (Ω[A⁄K])) (hω : Function.Bijective fun g : A => g • ω) :
    TopFormOrder.topFormMap K K A F d ω ≠ 0 := by sorry
