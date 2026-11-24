-- Prove2me | Theorems.Thm_GlobalTheory_NilRigidity_exists_preimage_quotient
-- name    : GlobalTheory.NilRigidity.exists_preimage_quotient
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T20:17:56.014883+00:00
-- url     : https://prove2.me/theorems/b7850e3c-c648-495e-bb37-721b35144c97
-- title:
--   Nil Rigidity: exists preimage quotient
-- statement:
--   The Nil Rigidity construction uses the exists preimage quotient property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/EqOfPullbackQuotientEq.lean#L13-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/EqOfPullbackQuotientEq.lean#L13-L22

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

theorem GlobalTheory.NilRigidity.exists_preimage_quotient {R : Type} [CommRing R] (I : Ideal R) (hI : I ≤ nilradical R) (t : Sp R) :
    ∃ t₀ : Sp (R ⧸ I), spMap (Ideal.Quotient.mk I) t₀ = t := by sorry
