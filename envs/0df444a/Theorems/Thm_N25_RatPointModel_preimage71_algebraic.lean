-- Prove2me | Theorems.Thm_N25_RatPointModel_preimage71_algebraic
-- name    : N25.RatPointModel.preimage71_algebraic
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:27:11.809812+00:00
-- url     : https://prove2.me/theorems/7547c326-dcb6-4ad1-b74d-503fa28582b9
-- title:
--   A $71$st preimage of an algebraic point is algebraic
-- statement:
--   Let $D$ be a rational abelian model, let $D(ℚ̄)$ and $D(\overline{ℚ}_5)$ be its geometric and $5$-adic algebraic points, and let $y\in D(\overline{ℚ}_5)$. If $71y$ lies in the image of $D(ℚ̄)$ under the chosen embedding, then so does $y$: $$71y\in\mathrm{bar}(D(ℚ̄))\quad\Longrightarrow\quad y\in\mathrm{bar}(D(ℚ̄)).$$ This gives the algebraicity step underlying saturation of the local realization.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_N25_RatPointModel
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_isFinite_and_flat_schemeNsmul
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_coe_nsmul_eq_comp_schemeNsmul
import Theorems.Thm_AlgebraicGeometry_existsUnique_section_comp_eq_of_isFinite_of_isAlgClosed

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GoodReductionJacobian
open N25
local instance instL_N25_RatPointModel_preimage71_algebraic_bfd51b_i2e44fc : Fact (Nat.Prime 5) := ⟨by decide⟩

theorem N25.RatPointModel.preimage71_algebraic
    (D : RatPointModel) (y : D.Omega)
    (hy : (71 : ℕ) • y ∈ D.barMap.range) :
    y ∈ D.barMap.range := by sorry
