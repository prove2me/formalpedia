-- Prove2me | Theorems.Thm_GlobalTheory_ExtDescent_isPullback_of_baseChange
-- name    : GlobalTheory.ExtDescent.isPullback_of_baseChange
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T13:16:36.251878+00:00
-- url     : https://prove2.me/theorems/8ecf920b-2c3b-4dc3-bc5d-03cd596ffdd5
-- title:
--   Ext Descent: is Pullback of base Change
-- statement:
--   The Ext Descent construction uses the is Pullback of base Change property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/SplitTorusExtensionDescends.lean#L67-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/SplitTorusExtensionDescends.lean#L67-L92

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SABBaseChangeSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HomBaseChangeBijectiveOfLeNilradical
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_RingHomFlatCodescendsAlongFaithfullyFlat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsAffineHomOfFlatQuotientOfAffineKernel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_GrpObjOfDenseOpen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SplitTorusExtensionDescends
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ExtDescent
variable {S S₀ : Scheme.{0}} {f : S ⟶ S₀}

theorem GlobalTheory.ExtDescent.isPullback_of_baseChange [Flat f] [Surjective f] [QuasiCompact f] {T G B T₀ G₀ B₀ : Scheme.{0}}
    {i : T ⟶ G} {t : T ⟶ S} {q : G ⟶ B} {e : S ⟶ B} (H : IsPullback i t q e)
    {i₀ : T₀ ⟶ G₀} {t₀ : T₀ ⟶ S₀} {q₀ : G₀ ⟶ B₀} {e₀ : S₀ ⟶ B₀}
    {τ : T ⟶ T₀} {g : G ⟶ G₀} {φ : B ⟶ B₀} (hτ : IsPullback τ t t₀ f) (hγ : IsPullback g q q₀ φ)
    (hi : τ ≫ i₀ = i ≫ g) (he : f ≫ e₀ = e ≫ φ) : IsPullback i₀ t₀ q₀ e₀ := by sorry
