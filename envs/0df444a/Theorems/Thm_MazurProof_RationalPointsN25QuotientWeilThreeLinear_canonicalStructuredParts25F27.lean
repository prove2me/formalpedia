-- Prove2me | Theorems.Thm_MazurProof_RationalPointsN25QuotientWeilThreeLinear_canonicalStructuredParts25F27
-- name    : MazurProof.RationalPointsN25QuotientWeilThreeLinear.canonicalStructuredParts25F27
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:10:11.562137+00:00
-- url     : https://prove2.me/theorems/0e5fed2a-a9ae-44c6-9933-b2be8244aa4a
-- title:
--   Chart decomposition of the canonical model over $\mathbf F_{27}$
-- statement:
--   Let $\mathbf F_{27}=\mathbf F_3[v]/(v^3+2v+1)$. For the canonical level-$25$ model over $\mathbf F_{27}$, let $R_{27}$ be the regular $x$-chart pairs with $z\ne1$, $E_{27}$ the exceptional pairs with $z=1$, and $Y_{27},Z_{27}$ the normalized $y$- and $z$-chart solution sets. Then
--
--   $$(|R_{27}|,|E_{27}|,|Y_{27}|,|Z_{27}|)=(17,0,1,1).$$
--
--   This gives the complete structured chart data for the point count over $\mathbf F_{27}$.
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

theorem MazurProof.RationalPointsN25QuotientWeilThreeLinear.canonicalStructuredParts25F27 :
    (canonicalRegularPairs25Three f27Operations).card = 17 ∧
    (canonicalExceptionalPairs25Three f27Operations).card = 0 ∧
    (canonicalYChartPairs25Three f27Operations).card = 1 ∧
    (canonicalZChartValues25Three f27Operations).card = 1 := by sorry
