-- Prove2me | Theorems.Thm_NeronModelInfra_TopFormOrder_topFormMap_topFormMap
-- name    : NeronModelInfra.TopFormOrder.topFormMap_topFormMap
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.228905+00:00
-- url     : https://prove2.me/theorems/1060016b-7007-51c7-816c-56821836c51d
-- title:
--   Functoriality of `topFormMap` along a tower of algebras
-- statement:
--   Fix three commutative rings $R_1, R_2, R_3$ and three commutative rings $O_1, O_2, O_3$, all in one universe, together with algebra structures $R_1 \to R_2 \to R_3$ and $R_1 \to R_3$ forming a scalar tower, $R_i$-algebra structures on $O_i$ for $i = 1,2,3$, algebra structures $O_1 \to O_2 \to O_3$ and $O_1 \to O_3$ forming a scalar tower, and the compatibilities making the whole diagram commute: $R_1 \to O_2$ is a tower both through $O_1$ and through $R_2$, $R_2 \to O_3$ is a tower both through $O_2$ and through $R_3$, and $R_1 \to O_3$ is a tower both through $O_1$ and through $R_3$. Let $d$ be a natural number and let $\eta \in \bigwedge^d_{O_1}\Omega_{O_1/R_1}$. Here `topFormMap R' K' O F d` denotes the map $\bigwedge^d_{O}\Omega_{O/R'} \to \bigwedge^d_{F}\Omega_{F/K'}$ obtained, via the universal property of the exterior power, from the alternating map sending $(v_i)_{i<d}$ to the wedge of the images $\mathrm{KaehlerDifferential.map}\,(v_i)$; it is linear for the $O$-module structure on the target got by restricting scalars along $O \to F$. The assertion is that applying `topFormMap` from $(R_1,O_1)$ to $(R_2,O_2)$ and then from $(R_2,O_2)$ to $(R_3,O_3)$ to $\eta$ gives the same element of $\bigwedge^d_{O_3}\Omega_{O_3/R_3}$ as applying `topFormMap` from $(R_1,O_1)$ to $(R_3,O_3)$ directly.
--
--   This is the composition (functoriality) law for the canonical map on top-degree differential forms along a tower of algebras. It is used in the scheme-theoretic layer on differentials, where identities between local sections of top differentials obtained on one chart must be transported along a composite of affine maps.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NeronModelInfra_TopFormOrder_topFormMap_topFormMap.lean

import Mathlib
import Definitions.Def_NeronModelInfra_TopFormOrder

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NeronModelInfra.TopFormOrder

universe u

theorem NeronModelInfra.TopFormOrder.topFormMap_topFormMap
    (R₁ R₂ R₃ O₁ O₂ O₃ : Type u) [CommRing R₁] [CommRing R₂] [CommRing R₃]
    [CommRing O₁] [CommRing O₂] [CommRing O₃]
    [Algebra R₁ R₂] [Algebra R₂ R₃] [Algebra R₁ R₃] [IsScalarTower R₁ R₂ R₃]
    [Algebra R₁ O₁] [Algebra R₂ O₂] [Algebra R₃ O₃]
    [Algebra O₁ O₂] [Algebra O₂ O₃] [Algebra O₁ O₃] [IsScalarTower O₁ O₂ O₃]
    [Algebra R₁ O₂] [IsScalarTower R₁ O₁ O₂] [IsScalarTower R₁ R₂ O₂]
    [Algebra R₂ O₃] [IsScalarTower R₂ O₂ O₃] [IsScalarTower R₂ R₃ O₃]
    [Algebra R₁ O₃] [IsScalarTower R₁ O₁ O₃] [IsScalarTower R₁ R₃ O₃]
    (d : ℕ) (η : ⋀[O₁]^d (Ω[O₁⁄R₁])) :
    topFormMap R₂ R₃ O₂ O₃ d (topFormMap R₁ R₂ O₁ O₂ d η) = topFormMap R₁ R₃ O₁ O₃ d η := by sorry
