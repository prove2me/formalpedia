-- Prove2me | Theorems.Thm_GlobalTheory_exists_open_inter_fiber_subset_sectionComponent
-- name    : GlobalTheory.exists_open_inter_fiber_subset_sectionComponent
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T22:37:23.208015+00:00
-- url     : https://prove2.me/theorems/5cf1c7cc-8c36-4959-8627-d425e78a19f3
-- title:
--   Global Theory: exists open inter fiber subset section Component
-- statement:
--   The Global Theory construction uses the exists open inter fiber subset section Component property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsAffineChartPreirreducibleFiber.lean#L11-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsAffineChartPreirreducibleFiber.lean#L11-L37

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SectionComponentsPreimageOfIsPullbackStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsOpenConnectedComponentOfIsLocallyNoetherianStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ComponentInFibreIffOfIsPullbackStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsOpenIsIrreducibleComponentOfRationalPointSmootStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsAffineChartPreirreducibleFiber
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj
open GlobalTheory

theorem GlobalTheory.exists_open_inter_fiber_subset_sectionComponent (X S : Scheme.{0}) (f : X ⟶ S) (e : S ⟶ X)
    (hf : Smooth f) (he : e ≫ f = 𝟙 _) (s : S) :
    ∃ W₁ : X.Opens, e s ∈ W₁ ∧ ∀ x : X, x ∈ W₁ → f x = s →
      x ∈ connectedComponentIn (f ⁻¹' {s}) (e s) := by sorry
