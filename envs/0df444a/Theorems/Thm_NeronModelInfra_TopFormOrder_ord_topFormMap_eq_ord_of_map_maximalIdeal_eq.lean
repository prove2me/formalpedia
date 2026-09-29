-- Prove2me | Theorems.Thm_NeronModelInfra_TopFormOrder_ord_topFormMap_eq_ord_of_map_maximalIdeal_eq
-- name    : NeronModelInfra.TopFormOrder.ord_topFormMap_eq_ord_of_map_maximalIdeal_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.228905+00:00
-- url     : https://prove2.me/theorems/550b0d7e-23e2-5502-bcc7-e6debfc3b875
-- title:
--   Invariance of the order of a top form under index-one base change
-- statement:
--   All eight rings live in a single universe. Let $R$ and $R'$ be discrete valuation rings (commutative domains), with $R'$ an $R$-algebra whose structure map is local and satisfies $\mathfrak m_R R' = \mathfrak m_{R'}$, and let $K$, $K'$ be fraction fields of $R$, $R'$ with $K \to K'$ compatible with $R \to R'$. Let $O_0$ be a discrete valuation ring which is an $R$-algebra via a local map with $\mathfrak m_R O_0 = \mathfrak m_{O_0}$, with fraction field $F_0$ containing $K$; let $O$ be a discrete valuation ring which is an $R'$-algebra via a local map with $\mathfrak m_{R'} O = \mathfrak m_O$, with fraction field $F$ containing $K'$; and let $O_0 \to O$ be a local algebra map and $F_0 \to F$ a field extension, all compatible in the evident towers. Let $d : \mathbb N$ and let $b$ be an $O_0$-basis of $\Omega_{O_0/R}$ indexed by $\mathrm{Fin}\,d$. Assume the composite $O \otimes_{O_0} \Omega_{O_0/R} \to \Omega_{O/R} \to \Omega_{O/R'}$ (the base-change map followed by the functoriality map, restricted to $O$-linearity) is bijective, and that the element $\rho \in \bigwedge^d_F \Omega_{F/K'}$ obtained by sending $b_1, \dots, b_d$ into $\Omega_{O/R'}$, taking their exterior product and applying `topFormMap` is nonzero. Here `topFormMap R' K' O F d` denotes the canonical $O$-linear map $\bigwedge^d_O \Omega_{O/R'} \to \bigwedge^d_F \Omega_{F/K'}$ induced by $O \to F$, $R' \to K'$, and for $\omega$ in the target, `ord R' K' O d F` $\omega$ is defined to be the additive valuation `addOrd O F` $a$ (normalised so that a uniformiser of $O$ has value $1$, and $0$ at $0$) of a chosen $a \in F$ with $\omega = a\rho'$, whenever the image submodule `integralTopForms` of `topFormMap` is the $O$-span of a single $\rho'$ and such an $a$ exists, and $0$ otherwise. Then for every nonzero $a \in F_0$, writing $\omega_0 = a \cdot \mathrm{topFormMap}(b_1 \wedge \cdots \wedge b_d) \in \bigwedge^d_{F_0} \Omega_{F_0/K}$, the order of the image of $\omega_0$ in $\bigwedge^d_F \Omega_{F/K'}$ with respect to $O$ equals the order of $\omega_0$ itself with respect to $O_0$.
--
--   This is the invariance of the order of a top-degree differential form under a base change of ramification index one, as in Bosch–Lütkebohmert–Raynaud's treatment of Néron models and their minimal differential forms. It feeds into [`NeronModelInfra.TopFormOrder.eq_addOrd_and_bijective_mapBaseChange_of_topFormMap_eq_of_addOrd_le`](thm.html#NeronModelInfra.TopFormOrder.eq_addOrd_and_bijective_mapBaseChange_of_topFormMap_eq_of_addOrd_le), where orders of invariant forms on a scheme and on its base change along a smooth local ring are compared.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NeronModelInfra_TopFormOrder_ord_topFormMap_eq_ord_of_map_maximalIdeal_eq.lean

import Mathlib
import Definitions.Def_NeronModelInfra_TopFormOrder

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open TensorProduct NeronModelInfra.TopFormOrder

theorem NeronModelInfra.TopFormOrder.ord_topFormMap_eq_ord_of_map_maximalIdeal_eq
    (R R' K K' O₀ O F₀ F : Type u)
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R'] [Algebra R R'] [IsLocalHom (algebraMap R R')]
    (hRR' : Ideal.map (algebraMap R R') (IsLocalRing.maximalIdeal R) = IsLocalRing.maximalIdeal R')
    [Field K] [Algebra R K] [IsFractionRing R K] [Field K'] [Algebra R' K'] [IsFractionRing R' K']
    [Algebra K K'] [Algebra R K'] [IsScalarTower R K K'] [IsScalarTower R R' K']
    [CommRing O₀] [IsDomain O₀] [IsDiscreteValuationRing O₀] [Algebra R O₀] [IsLocalHom (algebraMap R O₀)]
    (hO₀ : Ideal.map (algebraMap R O₀) (IsLocalRing.maximalIdeal R) = IsLocalRing.maximalIdeal O₀)
    [Field F₀] [Algebra O₀ F₀] [IsFractionRing O₀ F₀] [Algebra K F₀] [Algebra R F₀]
    [IsScalarTower R O₀ F₀] [IsScalarTower R K F₀]
    [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra R' O] [IsLocalHom (algebraMap R' O)]
    (hO : Ideal.map (algebraMap R' O) (IsLocalRing.maximalIdeal R') = IsLocalRing.maximalIdeal O)
    [Field F] [Algebra O F] [IsFractionRing O F] [Algebra K' F] [Algebra R' F]
    [IsScalarTower R' O F] [IsScalarTower R' K' F]
    [Algebra O₀ O] [IsLocalHom (algebraMap O₀ O)] [Algebra R O] [IsScalarTower R O₀ O] [IsScalarTower R R' O]
    [Algebra F₀ F] [Algebra O₀ F] [IsScalarTower O₀ O F] [IsScalarTower O₀ F₀ F]
    [Algebra K F] [IsScalarTower K K' F] [IsScalarTower K F₀ F]
    (d : ℕ) (b : Module.Basis (Fin d) O₀ (Ω[O₀⁄R]))
    (hbc : Function.Bijective
      ((KaehlerDifferential.map R R' O O).restrictScalars O ∘ₗ KaehlerDifferential.mapBaseChange R O₀ O))
    (hρ : (letI := moduleAlong O F (⋀[F]^d (Ω[F⁄K']))
      topFormMap R' K' O F d (exteriorPower.ιMulti O d
        (fun i => KaehlerDifferential.map R R' O O (KaehlerDifferential.map R R O₀ O (b i))))) ≠ 0)
    (a : F₀) (ha : a ≠ 0) :
    letI := moduleAlong O₀ F₀ (⋀[F₀]^d (Ω[F₀⁄K]))
    letI := moduleAlong F₀ F (⋀[F]^d (Ω[F⁄K']))
    ord R' K' O d F (topFormMap K K' F₀ F d (a • topFormMap R K O₀ F₀ d (exteriorPower.ιMulti O₀ d b))) =
      ord R K O₀ d F₀ (a • topFormMap R K O₀ F₀ d (exteriorPower.ιMulti O₀ d b)) := by sorry
