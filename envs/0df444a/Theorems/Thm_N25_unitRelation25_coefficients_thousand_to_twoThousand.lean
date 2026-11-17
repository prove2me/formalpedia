-- Prove2me | Theorems.Thm_N25_unitRelation25_coefficients_thousand_to_twoThousand
-- name    : N25.unitRelation25_coefficients_thousand_to_twoThousand
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:56:34.211858+00:00
-- url     : https://prove2.me/theorems/bf80bdb0-9688-4554-beb1-9fa86d8f1fa5
-- title:
--   The cleared unit relation vanishes in degrees $1000$ through $1999$
-- statement:
--   Let $S(q)$ be the cleared unit-relation power series. For every integer $n$ with $1000≤n≤1999$, $$[q^n]S(q)=0.$$ This is the second verified coefficient block in the Sturm computation.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_N25_UnitRelationCertificate
import Definitions.Def_Polynomial_BinomialResidue
import Definitions.Def_N25_UnitRelation
import Definitions.Def_N25_UnitSeries

open N25

theorem N25.unitRelation25_coefficients_thousand_to_twoThousand :
    ∀ n : Fin 1000, PowerSeries.coeff (1000 + n.val) unitRelationClearedSeries25 = 0 := by sorry
