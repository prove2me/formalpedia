-- Prove2me | Theorems.Thm_GlobalTheory_UnitaryFrames_unitary_group_frames
-- name    : GlobalTheory.UnitaryFrames.unitary_group_frames
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:03:02.990914+00:00
-- url     : https://prove2.me/theorems/20e95609-1db6-4217-b0d4-244af1ed1941
-- title:
--   Unitary Frames: unitary group frames
-- statement:
--   The Unitary Frames construction uses the unitary group frames property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/DetNeZeroOfIsOrth.lean#L137-L172
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/DetNeZeroOfIsOrth.lean#L137-L172

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_DetNeZeroOfIsOrth
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix ComplexConjugate
open GlobalTheory GlobalTheory.UnitaryFrames
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem GlobalTheory.UnitaryFrames.unitary_group_frames :
    ((∀ (r : ℕ) (X : Data E r), ∃ H : Subgroup (X.Ψ → GL (Fin r) ℂ), ∀ g, g ∈ H ↔ X.IsUnitaryC fun τ => (g τ : Matrix (Fin r) (Fin r) ℂ)) ∧ (∀ (r : ℕ) (X : Data E r) (H : Subgroup (X.Ψ → GL (Fin r) ℂ)), (∀ g, g ∈ H ↔ X.IsUnitaryC fun τ => (g τ : Matrix (Fin r) (Fin r) ℂ)) → LocallyCompactSpace H ∧ SecondCountableTopology H ∧ ∀ x0, IsOrth X x0 → (∀ g : H, IsOrth X (X.lmulC (fun τ => ((g : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ)) x0)) ∧ ∃ ι : Frame X.Ψ r → H, ContinuousOn ι {x | IsOrth X x} ∧ (∀ x, IsOrth X x → X.lmulC (fun τ => ((ι x : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ)) x0 = x) ∧ ∀ g : H, ι (X.lmulC (fun τ => ((g : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ)) x0) = g)) := by sorry
