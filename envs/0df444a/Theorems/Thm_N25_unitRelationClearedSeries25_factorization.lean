-- Prove2me | Theorems.Thm_N25_unitRelationClearedSeries25_factorization
-- name    : N25.unitRelationClearedSeries25_factorization
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:50:45.671762+00:00
-- url     : https://prove2.me/theorems/6df0c49d-6e68-41c0-9553-645bb3244e0a
-- title:
--   The cleared relation factors through an explicit numerator polynomial and a unit
-- statement:
--   Let $S$ be the cleared relation series, let $P_0,P_1,P_2$ be the three unit-pair series, let $η_{unit}$ be the normalized eta unit, and let $R_{num}$ be the explicit numerator expression. Then $$S(P_1^5P_2^4)=X^{29}(η_{unit}^3)^{11}R_{num}(X,P_0,P_1,P_2),\qquad P_1^5P_2^4\text{ is a unit}.$$ This reduces the relation to a finite polynomial coefficient calculation.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_UnitRelation
import Definitions.Def_N25_UnitRelationCertificate

set_option autoImplicit false
open scoped BigOperators
open N25

theorem N25.unitRelationClearedSeries25_factorization :
    unitRelationClearedSeries25 * ((unitPairSeries25 1)^5 * (unitPairSeries25 2)^4) =
      PowerSeries.X^29 * (ModularCurve.dedekindEtaUnit^3)^11 *
        unitRelationNumerator25 PowerSeries.X
          (unitPairSeries25 0) (unitPairSeries25 1) (unitPairSeries25 2) ∧
      IsUnit ((unitPairSeries25 1)^5 * (unitPairSeries25 2)^4) := by sorry
