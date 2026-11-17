-- Prove2me | Theorems.Thm_MazurProof_RationalPointsN25QuotientKummerThreeProjective_f81_kummer_solutions_card
-- name    : MazurProof.RationalPointsN25QuotientKummerThreeProjective.f81_kummer_solutions_card
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:17:14.566827+00:00
-- url     : https://prove2.me/theorems/b4f0418b-4b5e-46f4-a94d-4d48e4d4a49c
-- title:
--   The Kummer equation has eighty-seven affine pairs over $\mathbf F_{81}$
-- statement:
--   Let $e\in\mathbf F_{81}$ be the chosen fifth-cyclotomic element, and let $K_e$ be the set of pairs $(r,t)\in\mathbf F_{81}^2$ satisfying $r^5D_e(t)+N_e(t)=0$. Then
--
--   $$|K_e|=87.$$
--
--   This packages the fiberwise computation as a single cardinality statement for the affine Kummer model.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_CanonicalThreeNormalization
import Definitions.Def_N25_CanonicalNormalizedPoints
import Definitions.Def_N25_NormalizedPointPivot
import Definitions.Def_N25_ExplicitKummerThreeF81
import Definitions.Def_N25_ExplicitKummerThreeProjective

open MazurProof
open MazurProof.RationalPointsN25QuotientKummerThreeProjective
open MazurProof.RationalPointsN25QuotientF2
open MazurProof.RationalPointsN25QuotientWeil
open MazurProof.RationalPointsN25QuotientWeilThree
open MazurProof.RationalPointsN25QuotientKummerThree
open MazurProof.RationalPointsN25QuotientKummerThreeF81
open scoped BigOperators

theorem MazurProof.RationalPointsN25QuotientKummerThreeProjective.f81_kummer_solutions_card :
    Nat.card (KummerSolutions f81FifthRoot25) = 87 := by sorry
