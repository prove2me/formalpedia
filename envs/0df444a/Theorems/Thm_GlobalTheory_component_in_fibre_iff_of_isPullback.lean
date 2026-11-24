-- Prove2me | Theorems.Thm_GlobalTheory_component_in_fibre_iff_of_isPullback
-- name    : GlobalTheory.component_in_fibre_iff_of_isPullback
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T22:13:33.447179+00:00
-- url     : https://prove2.me/theorems/955d8fd9-e882-4a8d-a67d-d5ca3ac628e4
-- title:
--   Global Theory: component in fibre iff of is Pullback
-- statement:
--   The Global Theory construction uses the component in fibre iff of is Pullback property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ComponentInFibreIffOfIsPullback.lean#L25-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ComponentInFibreIffOfIsPullback.lean#L25-L40

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ComponentInFibreIffOfIsPullback
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

theorem GlobalTheory.component_in_fibre_iff_of_isPullback :
    ∀ (X S : Scheme.{0}) (f : X ⟶ S) (e : S ⟶ X) (s : S) (Y : Scheme.{0}) (g : Y ⟶ Spec (S.residueField s))
      (q : Y ⟶ X) (y₀ : Y), IsPullback q g f (S.fromSpecResidueField s) → q y₀ = e s →
      ∀ y : Y, q y ∈ connectedComponentIn (f ⁻¹' {s}) (e s) ↔ y ∈ connectedComponent y₀ := by sorry
