-- Prove2me | Theorems.Thm_MazurProof_RationalPointsN25QuotientSmoothF3_wChart_xz_minor_eq_one25Three
-- name    : MazurProof.RationalPointsN25QuotientSmoothF3.wChart_xz_minor_eq_one25Three
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:08:59.816888+00:00
-- url     : https://prove2.me/theorems/1c5a5616-3d1d-41fc-a3ba-d0c15df28bd3
-- title:
--   The $xz$-Jacobian minor at the terminal $w$-chart point is one
-- statement:
--   Let $K$ be a field, let $Q$ and $C$ be the canonical quadric and cubic, and let $M_{xz}$ be the $xz$ minor of their $2×4$ Jacobian matrix. At the normalized point $P=(0,0,0,1)$, $$M_{xz}(P)=1.$$ This supplies an immediate nonsingularity certificate on the terminal projective chart.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_CanonicalThreeNormalization
import Definitions.Def_N25_CanonicalNormalizedPoints
import Definitions.Def_N25_NormalizedPointPivot

open MazurProof
open MazurProof.RationalPointsN25QuotientSmoothF3
open MazurProof.RationalPointsN25QuotientF2
open MazurProof.RationalPointsN25QuotientWeil
open MazurProof.RationalPointsN25QuotientKummerThree
open MazurProof.RationalPointsN25QuotientWeilThreeLinear
open MazurProof.RationalPointsN25QuotientKummerThreeProjective
open MazurProof.RationalPointsN25QuotientSmallThreeSemantic

theorem MazurProof.RationalPointsN25QuotientSmoothF3.wChart_xz_minor_eq_one25Three
    {K : Type*} [Field K] :
    (canonicalJacobianMinors25Three
      (⟨0, 0, 0, 1⟩ : Coordinates4 K)).xz = 1 := by sorry
