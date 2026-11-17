-- Prove2me | Theorems.Thm_MazurProof_RationalPointsN25QuotientWeilThreeLinear_canonicalStructuredParts25F9
-- name    : MazurProof.RationalPointsN25QuotientWeilThreeLinear.canonicalStructuredParts25F9
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:10:18.684197+00:00
-- url     : https://prove2.me/theorems/51408abd-9689-4407-b093-190e0da775c1
-- title:
--   Chart decomposition of the canonical model over $\mathbf F_9$
-- statement:
--   Let $\mathbf F_9=\mathbf F_3[u]/(u^2+2u+2)$. For the canonical level-$25$ model over $\mathbf F_9$, let $R_9$ be the regular $x$-chart pairs with $z\ne1$, $E_9$ the exceptional pairs with $z=1$, and $Y_9,Z_9$ the normalized $y$- and $z$-chart solution sets. Then
--
--   $$(|R_9|,|E_9|,|Y_9|,|Z_9|)=(2,0,1,1).$$
--
--   This gives the complete structured chart data for the point count over $\mathbf F_9$.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_ExplicitWeil
import Definitions.Def_N25_ExplicitWeilThreeDefs
import Definitions.Def_N25_CanonicalThreeNormalization
import Definitions.Def_N25_CanonicalNormalizedPoints
import Definitions.Def_N25_NormalizedPointPivot
import Definitions.Def_N25_ExplicitWeilThreeLinear

open MazurProof
open MazurProof.RationalPointsN25QuotientWeilThreeLinear
open MazurProof.RationalPointsN25QuotientWeil
open MazurProof.RationalPointsN25QuotientWeilThree
attribute [local instance] Fintype.decidableForallFintype
  Fintype.decidableExistsFintype

theorem MazurProof.RationalPointsN25QuotientWeilThreeLinear.canonicalStructuredParts25F9 :
    (canonicalRegularPairs25Three f9Operations).card = 2 ∧
    (canonicalExceptionalPairs25Three f9Operations).card = 0 ∧
    (canonicalYChartPairs25Three f9Operations).card = 1 ∧
    (canonicalZChartValues25Three f9Operations).card = 1 := by sorry
