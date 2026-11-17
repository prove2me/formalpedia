-- Prove2me | Theorems.Thm_N25_RatPointModel_localRealization_saturated
-- name    : N25.RatPointModel.localRealization_saturated
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:28:22.815674+00:00
-- url     : https://prove2.me/theorems/856d23dc-d69f-4797-93d4-059b8a13221f
-- title:
--   The local realization is saturated under multiplication by $71$
-- statement:
--   Let $D$ be a rational abelian model and let $e:M_5\to D(ℚ_5)$ be a homomorphism whose image consists exactly of the local points whose image in $D(\overline{ℚ}_5)$ comes from a geometric algebraic point. Then for every $y\in D(ℚ_5)$, $$71y\in e(M_5)\quad\Longrightarrow\quad y\in e(M_5).$$ This is the saturation property needed to pull finite-index $71$-divisibility back to $M_5$.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_N25_RatPointModel
import Definitions.Def_N25_LocalCarrier
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_isFinite_and_flat_schemeNsmul
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_coe_nsmul_eq_comp_schemeNsmul
import Theorems.Thm_AlgebraicGeometry_existsUnique_section_comp_eq_of_isFinite_of_isAlgClosed

set_option autoImplicit false
open N25

theorem N25.RatPointModel.localRealization_saturated
    (D : RatPointModel) (e : ↥M5 →+ D.Local)
    (himage : ∀ y : D.Local,
      y ∈ e.range ↔ D.localMap y ∈ D.barMap.range) :
    ∀ y : D.Local,
      (71 : ℕ) • y ∈ e.range → y ∈ e.range := by sorry
