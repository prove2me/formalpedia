-- Prove2me | Theorems.Thm_GlobalTheory_ExtDescent_fpqc_of_isPullback
-- name    : GlobalTheory.ExtDescent.fpqc_of_isPullback
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:34:21.897689+00:00
-- url     : https://prove2.me/theorems/b3e9c4ec-2101-408c-a974-37b57cb87bcb
-- title:
--   Ext Descent: fpqc of is Pullback
-- statement:
--   The Ext Descent construction uses the fpqc of is Pullback property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/SplitTorusExtensionDescends.lean#L60-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/SplitTorusExtensionDescends.lean#L60-L65

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

theorem GlobalTheory.ExtDescent.fpqc_of_isPullback [Flat f] [Surjective f] [QuasiCompact f] {X X₀ : Scheme.{0}} {p : X ⟶ X₀}
    {s : X ⟶ S} {s₀ : X₀ ⟶ S₀} (h : IsPullback p s s₀ f) :
    (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{0}) p := by sorry
