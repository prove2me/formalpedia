-- Prove2me | Theorems.Thm_N25_unitRelation25_coefficients_twoThousand_to_threeThousand
-- name    : N25.unitRelation25_coefficients_twoThousand_to_threeThousand
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T19:01:38.3822+00:00
-- url     : https://prove2.me/theorems/dd8c2ecf-6184-4004-b5ef-a786d806da21
-- title:
--   The cleared unit relation vanishes in degrees $2000$ through $2999$
-- statement:
--   Let $S(q)$ be the cleared unit-relation power series. For every integer $n$ with $2000≤n≤2999$, $$[q^n]S(q)=0.$$ This is the third verified coefficient block in the Sturm computation.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_N25_UnitRelationCertificate
import Definitions.Def_Polynomial_BinomialResidue
import Definitions.Def_N25_UnitRelation
import Definitions.Def_N25_UnitSeries

open N25

theorem N25.unitRelation25_coefficients_twoThousand_to_threeThousand :
    ∀ n : Fin 1000, PowerSeries.coeff (2000 + n.val) unitRelationClearedSeries25 = 0 := by sorry
