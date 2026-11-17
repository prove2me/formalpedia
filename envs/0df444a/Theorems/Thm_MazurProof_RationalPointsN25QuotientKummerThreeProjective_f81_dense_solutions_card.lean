-- Prove2me | Theorems.Thm_MazurProof_RationalPointsN25QuotientKummerThreeProjective_f81_dense_solutions_card
-- name    : MazurProof.RationalPointsN25QuotientKummerThreeProjective.f81_dense_solutions_card
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:17:51.069582+00:00
-- url     : https://prove2.me/theorems/3cb321b1-fdae-49e1-ba06-31d176ba6a2c
-- title:
--   The dense Segre chart has eighty-six solutions over $\mathbf F_{81}$
-- statement:
--   Let $e\in\mathbf F_{81}$ be the chosen fifth-cyclotomic element. Let $D_e$ be the set of pairs $(r,s)\in\mathbf F_{81}^2$ satisfying the dense-chart Segre cubic obtained after diagonalizing the order-five action. Then
--
--   $$|D_e|=86.$$
--
--   This removes the single spurious solution created by the denominator-cleared Kummer substitution.
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

theorem MazurProof.RationalPointsN25QuotientKummerThreeProjective.f81_dense_solutions_card :
    Nat.card (DenseSolutions f81FifthRoot25) = 86 := by sorry
