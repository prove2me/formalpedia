-- Prove2me | Theorems.Thm_NeronModelInfra_TopFormOrder_integralTopForms_eq_span_and_ord_smul_of_basis
-- name    : NeronModelInfra.TopFormOrder.integralTopForms_eq_span_and_ord_smul_of_basis
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.228905+00:00
-- url     : https://prove2.me/theorems/d258da44-9d01-5b22-ae91-3a284904dd9d
-- title:
--   Integral top forms cyclic on a basis wedge; ord(aρ)=ord(a)
-- statement:
--   Fix, all in a single universe, commutative rings $R'$ and $K'$ with $K'$ an $R'$-algebra, a commutative ring $O$ which is a domain and a discrete valuation ring and an $R'$-algebra, and a field $F$ which is an $O$-algebra realised as the fraction field of $O$, and also a $K'$-algebra and an $R'$-algebra, the scalar towers $R'\to O\to F$ and $R'\to K'\to F$ being compatible. Let $d\in\mathbb{N}$ and let $b$ be a basis of the $O$-module $\Omega_{O/R'}$ indexed by $\mathrm{Fin}\,d$. Regard $\bigwedge^d_F\Omega_{F/K'}$ as an $O$-module by restriction of scalars along $O\to F$, and write $\rho$ for the image under `topFormMap` — the $O$-linear map $\bigwedge^d_O\Omega_{O/R'}\to\bigwedge^d_F\Omega_{F/K'}$ induced by the alternating map `ιMultiAlong` — of the wedge $b_0\wedge\dots\wedge b_{d-1}$ of the basis vectors. Then two assertions hold. First, `integralTopForms`, by definition the range of `topFormMap`, is the $O$-submodule of $\bigwedge^d_F\Omega_{F/K'}$ spanned by the single element $\rho$. Second, for every $a\in F$ with $a\neq 0$, if moreover $\rho\neq 0$, then `ord` of $a\cdot\rho$ equals `addOrd` of $a$; here `addOrd` is the normalised additive valuation on $F$ attached to the maximal ideal of $O$ (value $0$ at $a=0$, and otherwise the negative of the additive value of that height-one valuation), and `ord` of a form $\omega$ is defined by choosing, when one exists, a generator $\rho'$ of `integralTopForms` together with a scalar $a'\in F$ with $\omega=a'\rho'$ and returning `addOrd` of that chosen $a'$, and $0$ otherwise.
--
--   This is the computation of the lattice of integral top-degree differential forms when the module of differentials of the local ring is free: the lattice is cyclic on the wedge of a basis, and the order function defined by an arbitrary choice of generator agrees with the valuation of the scalar, since two generators of a cyclic torsion-free module differ by a unit. It underlies the reading off of components in the Néron-model infrastructure and is used by [`NeronModelInfra.ComponentReading.eq_n_of_forall_topFormMap_eq_mul_zpow_smul`](thm.html#NeronModelInfra.ComponentReading.eq_n_of_forall_topFormMap_eq_mul_zpow_smul), [`NeronModelInfra.ComponentReading.n_le_n_and_isOpenImmersion_of_n_eq_of_specializes`](thm.html#NeronModelInfra.ComponentReading.n_le_n_and_isOpenImmersion_of_n_eq_of_specializes) and [`NeronModelInfra.TopFormOrder.eq_addOrd_and_bijective_mapBaseChange_of_topFormMap_eq_of_addOrd_le`](thm.html#NeronModelInfra.TopFormOrder.eq_addOrd_and_bijective_mapBaseChange_of_topFormMap_eq_of_addOrd_le).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NeronModelInfra_TopFormOrder_integralTopForms_eq_span_and_ord_smul_of_basis.lean

import Mathlib
import Definitions.Def_NeronModelInfra_TopFormOrder

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open NeronModelInfra.TopFormOrder

theorem NeronModelInfra.TopFormOrder.integralTopForms_eq_span_and_ord_smul_of_basis
    (R' K' O F : Type u) [CommRing R'] [CommRing K'] [Algebra R' K']
    [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra R' O]
    [Field F] [Algebra O F] [IsFractionRing O F] [Algebra K' F] [Algebra R' F]
    [IsScalarTower R' O F] [IsScalarTower R' K' F]
    (d : ℕ) (b : Module.Basis (Fin d) O (Ω[O⁄R'])) :
    letI := moduleAlong O F (⋀[F]^d (Ω[F⁄K']))
    integralTopForms R' K' O F d =
        Submodule.span O {topFormMap R' K' O F d (exteriorPower.ιMulti O d b)} ∧
      ∀ a : F, a ≠ 0 → topFormMap R' K' O F d (exteriorPower.ιMulti O d b) ≠ 0 →
        ord R' K' O d F (a • topFormMap R' K' O F d (exteriorPower.ιMulti O d b)) = addOrd O F a := by sorry
