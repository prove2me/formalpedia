-- Prove2me | Theorems.Thm_GlobalTheory_FieldBaseChange_exists_expansion
-- name    : GlobalTheory.FieldBaseChange.exists_expansion
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:06:42.981806+00:00
-- url     : https://prove2.me/theorems/3d7fc5a0-e5d7-4288-bf19-f56ad4a93740
-- title:
--   Field Base Change: exists expansion
-- statement:
--   The Field Base Change construction uses the exists expansion property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/IsExtensionOfIsPushout.lean#L52-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/IsExtensionOfIsPushout.lean#L52-L78

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IsExtensionOfIsPushout
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.FieldBaseChange
variable {K F : Type} [Field K] [Field F] [Algebra K F]
variable {V W : Type} [AddCommGroup V] [Module K V] [AddCommGroup W] [Module F W]

theorem GlobalTheory.FieldBaseChange.exists_expansion {ι : Type} (b : Module.Basis ι K F) {a : V →ₛₗ[algebraMap K F] W}
    (h : Submodule.span F (Set.range a) = ⊤) {Λ : ι → W →+ V} (hΛ : ∀ i, IsCoord a (b.coord i) (Λ i))
    (x : W) : ∃ S : Finset ι, (∀ i ∉ S, Λ i x = 0) ∧
      ∀ S' : Finset ι, S ⊆ S' → x = ∑ i ∈ S', b i • a (Λ i x) := by sorry
