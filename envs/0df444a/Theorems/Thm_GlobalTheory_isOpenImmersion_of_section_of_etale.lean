-- Prove2me | Theorems.Thm_GlobalTheory_isOpenImmersion_of_section_of_etale
-- name    : GlobalTheory.isOpenImmersion_of_section_of_etale
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:52:38.42013+00:00
-- url     : https://prove2.me/theorems/a5ce3ae9-5851-4570-a9fa-76b3960ea71e
-- title:
--   Global Theory: is Open Immersion of section of etale
-- statement:
--   The Global Theory construction uses the is Open Immersion of section of etale property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsUniqueDescendOfTorsionInvariant.lean#L13-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsUniqueDescendOfTorsionInvariant.lean#L13-L18

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_FnOfComp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueDescendOfTorsionInvariant
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory

theorem GlobalTheory.isOpenImmersion_of_section_of_etale {X S : Scheme.{0}} (f : X ⟶ S) [Etale f] (s : S ⟶ X)
    (hs : s ≫ f = 𝟙 S) : IsOpenImmersion s := by sorry
