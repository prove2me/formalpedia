-- Prove2me | Theorems.Thm_GlobalTheory_NilRigidity_eq_of_pullback_quotient_eq
-- name    : GlobalTheory.NilRigidity.eq_of_pullback_quotient_eq
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:21:40.654967+00:00
-- url     : https://prove2.me/theorems/9d571c46-6a9b-5486-b8b1-7ac942040820
-- title:
--   Nil Rigidity: eq of pullback quotient eq
-- statement:
--   The Nil Rigidity construction uses the eq of pullback quotient eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/EqOfPullbackQuotientEq.lean#L57-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/EqOfPullbackQuotientEq.lean#L57-L71

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsCompletedStrictHens
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_EqCompSectionOfSurjectiveAppTop
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SurjectiveAppOfIsAbelianScheme
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_GlobalFnsHolds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EqOfPullbackQuotientEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.NilRigidity

theorem GlobalTheory.NilRigidity.eq_of_pullback_quotient_eq {R : Type} [CommRing R] (I : Ideal R) (hI : IsNilpotent I)
    (B B' : Over (Sp R)) [GrpObj B] [GrpObj B'] (hB : IsAbelianScheme B) (f g : B ⟶ B') [IsMonHom f] [IsMonHom g]
    (h : (Over.pullback (spMap (Ideal.Quotient.mk I))).map f = (Over.pullback (spMap (Ideal.Quotient.mk I))).map g) :
    f = g := by sorry
