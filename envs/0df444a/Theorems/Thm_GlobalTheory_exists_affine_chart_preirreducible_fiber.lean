-- Prove2me | Theorems.Thm_GlobalTheory_exists_affine_chart_preirreducible_fiber
-- name    : GlobalTheory.exists_affine_chart_preirreducible_fiber
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T22:30:21.172956+00:00
-- url     : https://prove2.me/theorems/ae321659-dbcf-4fd7-8877-7f00949f6ec1
-- title:
--   Global Theory: exists affine chart preirreducible fiber
-- statement:
--   The Global Theory construction uses the exists affine chart preirreducible fiber property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsAffineChartPreirreducibleFiber.lean#L39-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsAffineChartPreirreducibleFiber.lean#L39-L80

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

theorem GlobalTheory.exists_affine_chart_preirreducible_fiber : ∀ (X S : Scheme.{0}) (f : X ⟶ S) (e : S ⟶ X), Smooth f → e ≫ f = 𝟙 _ → ∀ s : S, ∃ (V : S.Opens) (W : X.Opens) (_ : W ≤ f ⁻¹ᵁ V), IsAffineOpen V ∧ IsAffineOpen W ∧ e s ∈ W ∧ ∀ (k : Type) [Field k] (p : Spec (CommRingCat.of k) ⟶ S), p (IsLocalRing.closedPoint k) = s → PreirreducibleSpace ↥(pullback (W.ι ≫ f) p) := by sorry
