-- Prove2me | Theorems.Thm_GlobalTheory_AbLocusPull_abLocus_sections_pull
-- name    : GlobalTheory.AbLocusPull.abLocus_sections_pull
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T10:52:19.629819+00:00
-- url     : https://prove2.me/theorems/a0553513-d2d4-4ad6-80b6-88151ad40d5b
-- title:
--   Ab Locus Pull: ab Locus sections pull
-- statement:
--   The Ab Locus Pull construction uses the ab Locus sections pull property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/IsProperRestrictPull.lean#L175-L208
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/IsProperRestrictPull.lean#L175-L208

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AbProj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_OneArc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsProperRestrictPull
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory GlobalTheory.AbLocusPull
variable {X Y Z : Scheme.{0}}

theorem GlobalTheory.AbLocusPull.abLocus_sections_pull : ∀ (X X' : Scheme.{0}) (f : X' ⟶ X) (G : Over X) [GrpObj G] (G' : Over X') [GrpObj G'] (φ : G'.left ⟶ G.left), IsSemiAbelian G → IsGrpPullback G' G f φ → ((∃ U : X.Opens, (U : Set X) = abLocus G ∧ IsProper (G.hom ∣_ U)) → (∃ U : X'.Opens, (U : Set X') = abLocus G' ∧ IsProper (G'.hom ∣_ U))) ∧ ∀ (L : LB G.left) (L' : LB G'.left), L.IsLB → L'.IsLB → LBIso L' (L.pull φ) → (∀ x : X, ∃ V : X.Opens, x ∈ V ∧ ∃ θ ∈ secOn L (G.hom ⁻¹ᵁ V), ∀ y ∈ V, ∃ (g : G.left) (i : L.ι), G.hom g = y ∧ g ∈ G.left.basicOpen (θ i)) → (∀ x : X', ∃ V : X'.Opens, x ∈ V ∧ ∃ θ ∈ secOn L' (G'.hom ⁻¹ᵁ V), ∀ y ∈ V, ∃ (g : G'.left) (i : L'.ι), G'.hom g = y ∧ g ∈ G'.left.basicOpen (θ i)) := by sorry
