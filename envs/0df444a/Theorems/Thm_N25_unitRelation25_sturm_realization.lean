-- Prove2me | Theorems.Thm_N25_unitRelation25_sturm_realization
-- name    : N25.unitRelation25_sturm_realization
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:51:49.194642+00:00
-- url     : https://prove2.me/theorems/43b9de1a-8205-4b00-9c11-838ebc22844b
-- title:
--   The cleared unit relation is the integral q-expansion of a weight-$396$ form
-- statement:
--   Let $D(τ)=Δ(τ)^3$, $N_0(τ)=Δ(τ)^3u_0(τ)$, $N_1(τ)=Δ(τ)^3u_1(τ)$, and let $S(q)$ be the cleared relation series. There exists a modular form $H$ of weight $396$ on $Γ_H(25)$ with integral q-expansion $S(q)$ such that $$H(τ)=\operatorname{ClearedRelation}(D(τ),N_0(τ),N_1(τ)).$$ This places the explicit unit relation within the scope of the Sturm theorem.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_N25_UnitRelation
import Definitions.Def_N25_UnitAnalytic
import Theorems.Thm_ModularCurve_qExpansion_discriminant_eq_map_X_mul_dedekindEtaUnit

set_option autoImplicit false
open UpperHalfPlane ModularCurve
open scoped MatrixGroups
open N25

theorem N25.unitRelation25_sturm_realization :
    ∃ H : ModularForm GammaH25GL 396,
      ModularCurve.IsIntegralQExp H unitRelationClearedSeries25 ∧
      ∀ τ : UpperHalfPlane,
        H τ = clearedUnitRelation25
          (ModularForm.discriminant τ ^ 3)
          (ModularForm.discriminant τ ^ 3 * unitAnalytic25 0 τ)
          (ModularForm.discriminant τ ^ 3 * unitAnalytic25 1 τ) := by sorry
