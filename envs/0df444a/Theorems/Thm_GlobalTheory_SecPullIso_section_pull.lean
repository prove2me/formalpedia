-- Prove2me | Theorems.Thm_GlobalTheory_SecPullIso_section_pull
-- name    : GlobalTheory.SecPullIso.section_pull
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T11:49:24.545251+00:00
-- url     : https://prove2.me/theorems/72d2783d-a9fb-43da-9204-1be7fef7d4f8
-- title:
--   Sec Pull Iso: section pull
-- statement:
--   The Sec Pull Iso construction uses the section pull property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/SectionPull.lean#L84-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/SectionPull.lean#L84-L109

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SectionPull
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
open TopologicalSpace
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.SecPullIso

theorem GlobalTheory.SecPullIso.section_pull : ∀ (X X' : Scheme.{0}) (φ : X' ⟶ X) (H : LB X) (H' : LB X') (w : LB.Iso H' (H.pull φ)), H.IsLB → H'.IsLB → w.IsGen → ∀ s : LB.Sec H, (∃! s' : LB.Sec H', (∀ z (k : (H).ι) (k' : (H').ι), (φ) z ∈ (H).U k → z ∈ (H').U k' → gs (φ) z _ ((s).f k) = (Geo.Tor.gw (w) (𝟙 _) z k k').val * gs (𝟙 _) z _ ((s').f k'))) ∧ ∀ s' : LB.Sec H', (∀ z (k : (H).ι) (k' : (H').ι), (φ) z ∈ (H).U k → z ∈ (H').U k' → gs (φ) z _ ((s).f k) = (Geo.Tor.gw (w) (𝟙 _) z k k').val * gs (𝟙 _) z _ ((s').f k')) → nonzeroLocus s' = φ ⁻¹ᵁ nonzeroLocus s := by sorry
