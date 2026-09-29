-- Prove2me | Theorems.Thm_ModularCurve_DRLevel_isIntegral_and_isLocallyNoetherian_and_forall_stalk_pullback_toBase_specMap_rat
-- name    : ModularCurve.DRLevel.isIntegral_and_isLocallyNoetherian_and_forall_stalk_pullback_toBase_specMap_rat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.065378+00:00
-- url     : https://prove2.me/theorems/a899c236-6f90-5a58-8906-e25dd5c6acd9
-- title:
--   Generic fibre of the Igusa model of level Mq is Dedekind
-- statement:
--   Let $M$ be a nonzero natural number and $q$ a prime. Write $\mathfrak X =$ [`ModularCurve.IgusaScheme (M*q) q`](def/ModularCurve_IgusaScheme.html#L255), the scheme obtained as the pushout of the two chart morphisms `fFin (M*q) q` and `fInf (M*q) q`, and let `toBase M q` be its structure morphism `IgusaScheme.igusaTo (M*q) q` to $\operatorname{Spec}$ of the base ring `R q`, which by the type of `igusaTo` is $\mathbf Z$ localised at $q$, namely [`GaloisRep.ratLocalizedAt q`](def/GaloisRep_Flat.html#L8); this morphism is the one induced on the pushout by the two chart algebras `chartAlgFin` and `chartAlgInf` over that base. Let `specMap (R q) ℚ` denote $\operatorname{Spec}$ of the structure map $R q \to \mathbf Q$. The assertion is a conjunction of four statements about the fibre product $Y$ of `toBase M q` along `specMap (R q) ℚ`, that is, the generic fibre $\mathfrak X_{\mathbf Q}$: $Y$ is an integral scheme; $Y$ is locally Noetherian; for every point $y$ of $Y$ the stalk $\mathcal O_{Y,y}$ is integrally closed; and for every point $y$ of $Y$ the Krull dimension of $\mathcal O_{Y,y}$, as an element of the extended integers, is at most $1$.
--
--   This records that the generic fibre of the Igusa integral model of level $Mq$ over $\mathbf Z_{(q)}$ is a Dedekind scheme, the hypothesis under which divisor-theoretic and finiteness arguments on the modular curve over $\mathbf Q$ are available. It is used in the computation of the degrees of the two degeneracy maps in characteristic zero, in [`ModularCurve.DRModelPackageLevel.isFinite_flat_finrank_curveChange_heckeDegeneracy_rat`](thm.html#ModularCurve.DRModelPackageLevel.isFinite_flat_finrank_curveChange_heckeDegeneracy_rat) and [`ModularCurve.DRModelPackageLevel.finrank_pi_eq`](thm.html#ModularCurve.DRModelPackageLevel.finrank_pi_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRLevel_isIntegral_and_isLocallyNoetherian_and_forall_stalk_pullback_toBase_specMap_rat.lean

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageLevel
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve ModularCurve.DRLevel AlgebraicGeometry.SmoothProperCurve

theorem ModularCurve.DRLevel.isIntegral_and_isLocallyNoetherian_and_forall_stalk_pullback_toBase_specMap_rat
    (M q : ℕ) [NeZero M] [Fact q.Prime] :
    IsIntegral (pullback (toBase M q) (specMap (R q) ℚ)) ∧
    IsLocallyNoetherian (pullback (toBase M q) (specMap (R q) ℚ)) ∧
    (∀ y : ↥(pullback (toBase M q) (specMap (R q) ℚ)),
      IsIntegrallyClosed ((pullback (toBase M q) (specMap (R q) ℚ)).presheaf.stalk y)) ∧
    (∀ y : ↥(pullback (toBase M q) (specMap (R q) ℚ)),
      ringKrullDim ((pullback (toBase M q) (specMap (R q) ℚ)).presheaf.stalk y) ≤ 1) := by sorry
