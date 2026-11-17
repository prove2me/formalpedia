-- Prove2me | Theorems.Thm_N25_unitRelation25_sturm_coefficients
-- name    : N25.unitRelation25_sturm_coefficients
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T19:02:27.305143+00:00
-- url     : https://prove2.me/theorems/24ef8d92-eaaa-4ba5-90e4-1bc36bd2575e
-- title:
--   All coefficients below the weight-$396$ Sturm bound vanish
-- statement:
--   Let $S(q)$ be the cleared unit-relation series. Then for every integer $n$ with $0≤n<4951$, $$[q^n]S(q)=0.$$ This is the finite coefficient statement used to force the associated modular form to vanish identically.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_N25_UnitRelationCertificate
import Definitions.Def_Polynomial_BinomialResidue
import Definitions.Def_N25_UnitRelation
import Definitions.Def_N25_UnitSeries

open N25

theorem N25.unitRelation25_sturm_coefficients :
    ∀ n : Fin 4951, PowerSeries.coeff n.val unitRelationClearedSeries25 = 0 := by sorry
