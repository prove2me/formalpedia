-- Prove2me | Theorems.Thm_NeronModelInfra_TopFormOrder_span_topFormMap_iotaMulti_eq_top_and_exists_units_eq_smul_of_isLocalization_away
-- name    : NeronModelInfra.TopFormOrder.span_topFormMap_iotaMulti_eq_top_and_exists_units_eq_smul_of_isLocalization_away
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.228905+00:00
-- url     : https://prove2.me/theorems/190f7a63-6b6d-579a-8d57-61d69e017121
-- title:
--   Basis wedge generates top forms after inverting varpi
-- statement:
--   Let $R$, $K$, $B$, $B'$ be commutative rings in one universe, with $K$ an $R$-algebra, $\varpi \in R$, and $K$ a localisation of $R$ away from $\varpi$; let $B$ be an $R$-algebra, and let $B'$ carry compatible $B$-, $K$- and $R$-algebra structures, the two scalar towers $R \to B \to B'$ and $R \to K \to B'$ being assumed, with $B'$ a localisation of $B$ away from the image of $\varpi$ in $B$. Let $d \in \mathbb{N}$ and let $\beta$ be a $B$-basis of $\Omega_{B/R}$ indexed by $\mathrm{Fin}\,d$. The $B'$-module $\bigwedge^d_{B'} \Omega_{B'/K}$ is regarded also as a $B$-module by restriction of scalars along $B \to B'$, and `topFormMap` is the $B$-linear map $\bigwedge^d_{B} \Omega_{B/R} \to \bigwedge^d_{B'} \Omega_{B'/K}$ induced, via the correspondence between alternating maps and maps out of the exterior power, by the alternating map `ιMultiAlong` built from the base-change map on differentials. The assertion is twofold: the $B'$-span of the single element $\rho = \mathrm{topFormMap}(\beta_1 \wedge \dots \wedge \beta_d)$ is all of $\bigwedge^d_{B'} \Omega_{B'/K}$; and for every $\sigma \in \bigwedge^d_{B'} \Omega_{B'/K}$ whose $B'$-span is everything there is a unit $u \in B'^{\times}$ with $\sigma = u \cdot \rho$.
--
--   This is the algebraic content of the comparison of a top-degree differential form on a smooth $R$-model with one on its generic fibre: the wedge of a basis of $\Omega_{B/R}$ remains a generator after inverting $\varpi$, and generators are unique up to units of $B'$. It is used in the construction of the order of a top form along the special fibre, where a nowhere-vanishing generic top form is written as a unit times a power of $\varpi$ against the model basis wedge.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NeronModelInfra_TopFormOrder_span_topFormMap_iotaMulti_eq_top_and_exists_units_eq_smul_of_isLocalization_away.lean

import Mathlib
import Definitions.Def_NeronModelInfra_TopFormOrder

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open NeronModelInfra.TopFormOrder

theorem NeronModelInfra.TopFormOrder.span_topFormMap_iotaMulti_eq_top_and_exists_units_eq_smul_of_isLocalization_away
    (R K B B' : Type u) [CommRing R] [CommRing K] [Algebra R K] (ϖ : R) [IsLocalization.Away ϖ K]
    [CommRing B] [Algebra R B] [CommRing B'] [Algebra B B'] [Algebra K B'] [Algebra R B']
    [IsScalarTower R B B'] [IsScalarTower R K B'] [IsLocalization.Away (algebraMap R B ϖ) B']
    (d : ℕ) (β : Module.Basis (Fin d) B (Ω[B⁄R])) :
    letI := moduleAlong B B' (⋀[B']^d (Ω[B'⁄K]))
    Submodule.span B' {topFormMap R K B B' d (exteriorPower.ιMulti B d β)} = ⊤ ∧
      ∀ σ : ⋀[B']^d (Ω[B'⁄K]), Submodule.span B' {σ} = ⊤ →
        ∃ u : B'ˣ, σ = (u : B') • topFormMap R K B B' d (exteriorPower.ιMulti B d β) := by sorry
