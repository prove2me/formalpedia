-- Prove2me | Theorems.Thm_MazurProof_RationalPointsN25QuotientWeilThree_ternary_extension_cardinalities
-- name    : MazurProof.RationalPointsN25QuotientWeilThree.ternary_extension_cardinalities
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:11:28.573145+00:00
-- url     : https://prove2.me/theorems/e9b93e68-59aa-47a7-81a2-c0486c60ce6b
-- title:
--   Cardinalities of the ternary extension fields
-- statement:
--   Let $\mathbf F_3$ be the three-element base type, let $\mathbf F_9=\mathbf F_3[u]/(u^2+2u+2)$, let $\mathbf F_{27}=\mathbf F_3[v]/(v^3+2v+1)$, and let $\mathbf F_{81}=\mathbf F_3[q]/(q^4+2q^3+2)$. Then
--
--   $$|\mathbf F_3|=3,\qquad |\mathbf F_9|=9,\qquad |\mathbf F_{27}|=27,\qquad |\mathbf F_{81}|=81.$$
--
--   These cardinalities support the characteristic-three extension counts used in the second Weil computation.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_ExplicitWeil
import Definitions.Def_N25_ExplicitWeilThreeDefs
import Definitions.Def_N25_CanonicalThreeNormalization
import Definitions.Def_N25_CanonicalNormalizedPoints
import Definitions.Def_N25_NormalizedPointPivot
import Definitions.Def_N25_ExplicitWeilThreeLinear

open MazurProof
open MazurProof.RationalPointsN25QuotientWeilThree
open MazurProof.RationalPointsN25QuotientF2
open MazurProof.RationalPointsN25QuotientWeil

theorem MazurProof.RationalPointsN25QuotientWeilThree.ternary_extension_cardinalities :
    Fintype.card Trit = 3 ∧ Fintype.card F9 = 9 ∧
      Fintype.card F27 = 27 ∧ Fintype.card F81 = 81 := by sorry
