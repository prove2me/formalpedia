-- Prove2me | Theorems.Thm_NeronModelInfra_TopFormOrder_exists_basis_units_int_forall_topFormMap_eq_mul_zpow_smul_of_span_singleton_eq_top
-- name    : NeronModelInfra.TopFormOrder.exists_basis_units_int_forall_topFormMap_eq_mul_zpow_smul_of_span_singleton_eq_top
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.228905+00:00
-- url     : https://prove2.me/theorems/666a2824-2b0d-5038-8949-4503bff19a41
-- title:
--   Uniform Laurent form of a generating top differential form
-- statement:
--   Fix a universe and let $R$, $K$, $B$, $B'$, $O$ be commutative rings in it. Assume $K$ is a localisation of $R$ away from an element $\varpi\in R$; let $B$ be an $R$-algebra and $B'$ a ring that is simultaneously a $B$-, $K$- and $R$-algebra, compatibly (scalar towers $R\to B\to B'$ and $R\to K\to B'$), and that is the localisation of $B$ away from the image of $\varpi$. Let $d\in\mathbb{N}$, let $\beta$ be a $B$-basis of $\Omega_{B/R}$ indexed by $\mathrm{Fin}\,d$, and let $\sigma\in\bigwedge^d_{B'}\Omega_{B'/K}$ generate that module, i.e. $B'\cdot\sigma=\top$. Let $O$ be a noetherian domain that is an $R$- and $B$-algebra with $R\to B\to O$ a tower and that is the localisation of $B$ at a submonoid $M\subseteq B$; assume the image of $\varpi$ in $O$ is nonzero and generates a prime ideal. Then there are an $O$-basis $b'$ of $\Omega_{O/R}$ indexed by $\mathrm{Fin}\,d$, a unit $w\in O^\times$ and an integer $m$ such that $b'_i=\,$`KaehlerDifferential.map R R B O`$(\beta_i)$ for all $i$, and such that for every field $F$ carrying compatible $O$-, $R$-, $K$-, $B$- and $B'$-algebra structures (towers $R\to O\to F$, $R\to K\to F$, $B\to O\to F$, $R\to B\to F$, $B\to B'\to F$, $K\to B'\to F$) the image of $\sigma$ under `topFormMap K K B' F d` equals the image of $b'_1\wedge\dots\wedge b'_d$ under `topFormMap R K O F d` multiplied by the scalar $w\,\varpi^{m}\in F$ (images of $w$ and of $\varpi$ under $O\to F$, the integer power taken in the field $F$). Here `topFormMap R' K' O' F d` denotes the $O'$-linear comparison map $\bigwedge^d_{O'}\Omega_{O'/R'}\to\bigwedge^d_F\Omega_{F/K'}$ obtained from the canonical alternating map, the target being regarded as an $O'$-module through $O'\to F$.
--
--   This is the ring-theoretic core of the comparison, at a height-one prime, between a generating top-degree differential form over the localised ring and the form coming from a basis of differentials over the integral model, as in the treatment of Néron models by Bosch, Lütkebohmert and Raynaud (§4.3); the essential point is that the Laurent exponent $m$ and the unit $w$ are chosen once and for all, uniformly in the test field $F$. It is used in the reading off of components, via [`NeronModelInfra.ComponentReading.exists_basis_units_int_forall_topFormMap_eq_mul_zpow_smul_of_specializes`](thm.html#NeronModelInfra.ComponentReading.exists_basis_units_int_forall_topFormMap_eq_mul_zpow_smul_of_specializes).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NeronModelInfra_TopFormOrder_exists_basis_units_int_forall_topFormMap_eq_mul_zpow_smul_of_span_singleton_eq_top.lean

import Mathlib
import Definitions.Def_NeronModelInfra_TopFormOrder

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NeronModelInfra TopFormOrder

universe u

theorem NeronModelInfra.TopFormOrder.exists_basis_units_int_forall_topFormMap_eq_mul_zpow_smul_of_span_singleton_eq_top
    (R K B B' O : Type u) [CommRing R] [CommRing K] [Algebra R K] (ϖ : R) [IsLocalization.Away ϖ K]
    [CommRing B] [Algebra R B] [CommRing B'] [Algebra B B'] [Algebra K B'] [Algebra R B']
    [IsScalarTower R B B'] [IsScalarTower R K B'] [IsLocalization.Away (algebraMap R B ϖ) B']
    (d : ℕ) (β : Module.Basis (Fin d) B (Ω[B⁄R]))
    (σ : ⋀[B']^d (Ω[B'⁄K])) (hσ : Submodule.span B' {σ} = ⊤)
    [CommRing O] [IsDomain O] [IsNoetherianRing O] [Algebra B O] [Algebra R O] [IsScalarTower R B O]
    (M : Submonoid B) [IsLocalization M O]
    (hϖ0 : algebraMap R O ϖ ≠ 0) (hϖ : (Ideal.span {algebraMap R O ϖ}).IsPrime) :
    ∃ (b' : Module.Basis (Fin d) O (Ω[O⁄R])) (w : Oˣ) (m : ℤ),
      (∀ i, b' i = KaehlerDifferential.map R R B O (β i)) ∧
      ∀ (F : Type u) [Field F] [Algebra O F] [Algebra R F] [Algebra K F] [Algebra B F] [Algebra B' F]
        [IsScalarTower R O F] [IsScalarTower R K F] [IsScalarTower B O F] [IsScalarTower R B F]
        [IsScalarTower B B' F] [IsScalarTower K B' F],
        topFormMap K K B' F d σ =
          (algebraMap O F (w : O) * algebraMap O F (algebraMap R O ϖ) ^ m) •
            topFormMap R K O F d (exteriorPower.ιMulti O d b') := by sorry
