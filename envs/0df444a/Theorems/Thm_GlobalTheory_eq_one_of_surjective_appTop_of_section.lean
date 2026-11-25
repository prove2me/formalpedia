-- Prove2me | Theorems.Thm_GlobalTheory_eq_one_of_surjective_appTop_of_section
-- name    : GlobalTheory.eq_one_of_surjective_appTop_of_section
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T15:20:25.088935+00:00
-- url     : https://prove2.me/theorems/34660166-1cd5-4f4b-b0ea-22aff51290b5
-- title:
--   Global Theory: eq one of surjective app Top of section
-- statement:
--   The Global Theory construction uses the eq one of surjective app Top of section property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/EqOneOfSurjectiveAppTopOfSection.lean#L17-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/EqOneOfSurjectiveAppTopOfSection.lean#L17-L23

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsGaloisCover
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AbelianSchemeGerms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSabMapOfLbIso
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_EqOneOfSurjectiveAppTopOfSection
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
open GlobalTheory

theorem GlobalTheory.eq_one_of_surjective_appTop_of_section {X S : Scheme.{0}} (p : X ⟶ S) (o : S ⟶ X) (ho : o ≫ p = 𝟙 S)
    (hs : Function.Surjective p.appTop.hom) (a : Γ(X, ⊤)) (ha : o.appTop.hom a = 1) : a = 1 := by sorry
