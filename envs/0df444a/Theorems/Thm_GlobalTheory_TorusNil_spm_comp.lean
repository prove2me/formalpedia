-- Prove2me | Theorems.Thm_GlobalTheory_TorusNil_spm_comp
-- name    : GlobalTheory.TorusNil.spm_comp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:06:08.170549+00:00
-- url     : https://prove2.me/theorems/83468b67-260d-468e-8013-b6eb8b2056c8
-- title:
--   Torus Nil: spm comp
-- statement:
--   The Torus Nil construction uses the spm comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/SplitTorusHomEqOneOfNilpotent.lean#L33-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/SplitTorusHomEqOneOfNilpotent.lean#L33-L36

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegExp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SplitTorusHomEqOneOfNilpotent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory
open GlobalTheory.TorusNil
variable {A : Type} [CommRing A]
variable {C D E : Type} [CommRing C] [Algebra A C] [CommRing D] [Algebra A D]
  [CommRing E] [Algebra A E]

theorem GlobalTheory.TorusNil.spm_comp (φ : C →ₐ[A] D) (ψ : D →ₐ[A] E) : spm (ψ.comp φ) = spm ψ ≫ spm φ := by sorry
