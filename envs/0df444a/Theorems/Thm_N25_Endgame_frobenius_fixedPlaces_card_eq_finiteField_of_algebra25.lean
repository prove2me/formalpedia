-- Prove2me | Theorems.Thm_N25_Endgame_frobenius_fixedPlaces_card_eq_finiteField_of_algebra25
-- name    : N25.Endgame.frobenius_fixedPlaces_card_eq_finiteField_of_algebra25
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:35:12.436527+00:00
-- url     : https://prove2.me/theorems/66e72e9f-5b69-4573-ba5b-293faaf02e29
-- title:
--   Frobenius-fixed geometric places count degree-one finite-field places
-- statement:
--   Let $p$ be prime, let $k$ be a finite field of characteristic $p$, let $K$ be an algebraically closed field of characteristic $p$ with a specified $k$-algebra structure, and let $n>0$ satisfy $|k|=p^n$. Let $F_K$ be the level-$25$ function field over $K$, let $F_k$ be its finite-field form, and let $Fr_p$ act on places of $F_K$. Then
--
--   $$\bigl|Fix(Fr_p^n)\bigr|=\bigl|\{P∈Places_k(F_k):deg(P)=1\}\bigr|.$$
--
--   This converts a geometric Frobenius fixed-point count into the rational-place count over $k$. Formalization note: the given $k$-algebra structure specifies the chosen embedding $k→K$.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_Endgame
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_N25_UnitLaurentField
import Definitions.Def_N25_CoefficientMap
import Theorems.Thm_ModularCurve_qExpFunctionFieldC_eq_adjoin_image_coeffMap_qExpFunctionFieldC
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Definitions.Def_ModularCurve_X0ModL
import Theorems.Thm_ModularCurve_exists_transcendental_finiteDimensional_qExpFunctionFieldC_of_isAlgClosed
import Theorems.Thm_ModularCurve_finiteDimensional_and_finrank_adjoin_le_of_eq_coeffMap
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_transcendental_of_perfectField
import Theorems.Thm_AlgebraicCurve_essFiniteType_of_transcendental_of_finiteDimensional
import Theorems.Thm_AlgebraicCurve_finite_fixedPoints_restrictAlong_iterate_and_natCard_eq_sum_divisors

open N25
open N25.Endgame

theorem N25.Endgame.frobenius_fixedPlaces_card_eq_finiteField_of_algebra25
    (p : ℕ) [Fact p.Prime]
    (k : Type*) [Field k] [Finite k] [CharP k p]
    (K : Type*) [Field K] [IsAlgClosed K] [CharP K p] [Algebra k K]
    (n : ℕ) (hn : 0 < n) (hk : Nat.card k = p ^ n) :
    Nat.card (Function.fixedPoints ((ModularCurve.qExpFrobeniusPlaceModL K Γ25 p)^[n])) =
      Nat.card {P : AlgebraicCurve.Place k (FBase k) // P.deg = 1} := by sorry
