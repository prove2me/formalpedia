-- Prove2me | Theorems.Thm_GlobalTheory_ZM_IntegersAway_exists_tBase_fractionRing
-- name    : GlobalTheory.ZM.IntegersAway.exists_tBase_fractionRing
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:44:29.587698+00:00
-- url     : https://prove2.me/theorems/dd739531-98ee-4643-aa0c-14c456ace63d
-- title:
--   Integers Away: exists t Base fraction Ring
-- statement:
--   The Integers Away construction uses the exists t Base fraction Ring property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/IsPrimitiveRootMapOfNatCastNeZero.lean#L53-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/IsPrimitiveRootMapOfNatCastNeZero.lean#L53-L69

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsGaloisCover
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsPrimitiveRootMapOfNatCastNeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZM.IntegersAway

theorem GlobalTheory.ZM.IntegersAway.exists_tBase_fractionRing : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Level H), ∃ (o : Type) (_ : CommRing o) (b : TBase o l.A) (em : o →+* ℂ) (ρ : o) (_ : Algebra o (KA l)), ArBase em ∧ IsFractionRing o (KA l) ∧ (∀ x, ((algebraMap o (KA l) x : KA l) : ℂ) = em x) ∧ algebraMap o (KA l) ρ = (baseKA l).ρ ∧ algebraMap o (KA l) (b.ζ : o) = (baseKA l).ζ := by sorry
