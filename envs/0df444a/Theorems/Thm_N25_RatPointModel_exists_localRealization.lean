-- Prove2me | Theorems.Thm_N25_RatPointModel_exists_localRealization
-- name    : N25.RatPointModel.exists_localRealization
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:29:35.585358+00:00
-- url     : https://prove2.me/theorems/97c4213a-05cd-417f-94e2-311c41ceceec
-- title:
--   The locally fixed subgroup embeds exactly into the algebraic local points
-- statement:
--   Let $D$ be a rational abelian model of $J$, let $M_5=J^{G_{ℚ_5}}$, let $D(ℚ_5)$ be its local points, and let both $D(ℚ̄)$ and $D(ℚ_5)$ map to $D(\overline{ℚ}_5)$. There exists an injective homomorphism $e:M_5\to D(ℚ_5)$ such that $$\mathrm{loc}(e(x))=\mathrm{bar}(D.\mathrm{pts}(x))\quad(x\in M_5),$$ $$y\in e(M_5)\quad\Longleftrightarrow\quad \mathrm{loc}(y)\in\mathrm{bar}(D(ℚ̄)).$$ This identifies the local realization of the Galois-fixed subgroup and characterizes its image by algebraicity.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_N25_RatPointModel
import Definitions.Def_N25_LocalCarrier
import Theorems.Thm_AlgebraicGeometry_Scheme_exists_specMap_fixedField_comp_eq_of_forall_comp_eq

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open CategoryTheory AlgebraicGeometry GoodReductionJacobian
open N25
local instance instL_N25_RatPointModel_exists_localRealizatio_bfd51b_i6f0e77 : Fact (Nat.Prime 5) := ⟨by decide⟩
local instance instL_N25_RatPointModel_exists_localRealizatio_3dbe1c_i6f0e77 : IsScalarTower ℚ ℚ_[5] (PadicAlgCl 5) :=
  IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)

theorem N25.RatPointModel.exists_localRealization (D : RatPointModel) :
    ∃ e : ↥M5 →+ D.Local,
      Function.Injective e ∧
      (∀ x : ↥M5, D.localMap (e x) = D.barMap (D.pts (x : J))) ∧
      (∀ y : D.Local, y ∈ e.range ↔ D.localMap y ∈ D.barMap.range) := by sorry
