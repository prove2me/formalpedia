-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_PrimitiveExponentPullback_sameSum_prim
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.PrimitiveExponentPullback.sameSum_prim
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:11:34.390828+00:00
-- url     : https://prove2.me/theorems/ed4a1bf4-ae80-47b9-8dbb-78b48517a63b
-- title:
--   Primitive Exponent Pullback: same Sum prim
-- statement:
--   The Primitive Exponent Pullback construction uses the same Sum prim property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/CMModuli/PrimitiveExponentPullback.lean#L116-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/CMModuli/PrimitiveExponentPullback.lean#L116-L129

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_AbelianSchemeQuotients_IsAbelianScheme
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_CubicalStructures_CubicalPullBaseChangeSt
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_HostConjugateIdeal
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_PrimitiveExponentPullback
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField AlgebraicGeometry CategoryTheory Limits MonoidalCategory
  CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.PrimitiveExponentPullback
open GlobalTheory.IndefiniteRowSideFullHecke.HostConjugateIdeal
variable {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G]

theorem GlobalTheory.IndefiniteRowSideFullHecke.PrimitiveExponentPullback.sameSum_prim (w : G ⟶ G) :
    LB.SameSum (fun k => eSec G ≫ primPt G w k) primExp
      (fun _ : PUnit.{1} => eSec G) (fun _ => 1) := by sorry
