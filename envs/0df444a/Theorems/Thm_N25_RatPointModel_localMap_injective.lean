-- Prove2me | Theorems.Thm_N25_RatPointModel_localMap_injective
-- name    : N25.RatPointModel.localMap_injective
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:26:08.327631+00:00
-- url     : https://prove2.me/theorems/8426f868-8f9e-41c1-ae0c-5be91e185c93
-- title:
--   Base change from $ℚ_5$-points to $\overline{ℚ}_5$-points is injective
-- statement:
--   Let $D$ be a rational abelian model. The scalar-extension map from its $ℚ_5$-points to its points over the $5$-adic algebraic closure is injective: $$D(ℚ_5)\hookrightarrow D(\overline{ℚ}_5).$$ This permits divisibility and image conditions to be checked after passage to a common algebraically closed local field.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_N25_RatPointModel

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open CategoryTheory AlgebraicGeometry GoodReductionJacobian
open N25
local instance instL_N25_RatPointModel_localMap_injective_bfd51b_ia879a8 : Fact (Nat.Prime 5) := ⟨by decide⟩
local instance instL_N25_RatPointModel_localMap_injective_3dbe1c_ia879a8 : IsScalarTower ℚ ℚ_[5] (PadicAlgCl 5) :=
  IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)

theorem N25.RatPointModel.localMap_injective (D : RatPointModel) :
    Function.Injective D.localMap := by sorry
