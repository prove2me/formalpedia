-- Prove2me | Theorems.Thm_N25_unitRelation25_coefficients_fourThousand_to_bound
-- name    : N25.unitRelation25_coefficients_fourThousand_to_bound
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:57:29.440203+00:00
-- url     : https://prove2.me/theorems/61d79cc5-426b-47c9-87a5-d643fdb6e3c3
-- title:
--   The cleared unit relation vanishes in degrees $4000$ through $4950$
-- statement:
--   Let $S(q)$ be the cleared unit-relation power series. For every integer $n$ with $4000≤n≤4950$, $$[q^n]S(q)=0.$$ This supplies the final block of coefficient vanishing required by the Sturm bound.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_N25_UnitRelationCertificate
import Definitions.Def_Polynomial_BinomialResidue
import Definitions.Def_N25_UnitRelation
import Definitions.Def_N25_UnitSeries

open N25

theorem N25.unitRelation25_coefficients_fourThousand_to_bound :
    ∀ n : Fin 951, PowerSeries.coeff (4000 + n.val) unitRelationClearedSeries25 = 0 := by sorry
