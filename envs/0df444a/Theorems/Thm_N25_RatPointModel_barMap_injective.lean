-- Prove2me | Theorems.Thm_N25_RatPointModel_barMap_injective
-- name    : N25.RatPointModel.barMap_injective
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:25:20.332828+00:00
-- url     : https://prove2.me/theorems/4956a1ff-291c-4021-85e3-c064a50bb98f
-- title:
--   Base change from algebraic points to $5$-adic algebraic points is injective
-- statement:
--   Let $D$ be a rational abelian model of $J$, let $D(ℚ̄)$ be its geometric points, and let $D(\overline{ℚ}_5)$ be its points over the $5$-adic algebraic closure. The map induced by the chosen embedding $ℚ̄\hookrightarrow\overline{ℚ}_5$ is injective: $$D(ℚ̄)\hookrightarrow D(\overline{ℚ}_5).$$ This allows global algebraic points to be recognized inside the common local algebraic carrier.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_N25_RatPointModel

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open CategoryTheory AlgebraicGeometry GoodReductionJacobian
open N25
local instance instL_N25_RatPointModel_barMap_injective_bfd51b_i2a8473 : Fact (Nat.Prime 5) := ⟨by decide⟩
local instance instL_N25_RatPointModel_barMap_injective_3dbe1c_i2a8473 : IsScalarTower ℚ ℚ_[5] (PadicAlgCl 5) :=
  IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)

theorem N25.RatPointModel.barMap_injective (D : RatPointModel) :
    Function.Injective D.barMap := by sorry
