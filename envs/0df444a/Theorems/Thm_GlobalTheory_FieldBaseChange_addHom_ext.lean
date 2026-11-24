-- Prove2me | Theorems.Thm_GlobalTheory_FieldBaseChange_addHom_ext
-- name    : GlobalTheory.FieldBaseChange.addHom_ext
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T13:24:23.245487+00:00
-- url     : https://prove2.me/theorems/f31c1fbc-7e56-4435-93a1-cdd79a39339c
-- title:
--   Field Base Change: add Hom ext
-- statement:
--   The Field Base Change construction uses the add Hom ext property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/IsExtensionOfIsPushout.lean#L35-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/IsExtensionOfIsPushout.lean#L35-L39

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

theorem GlobalTheory.FieldBaseChange.addHom_ext {a : V →ₛₗ[algebraMap K F] W} (h : Submodule.span F (Set.range a) = ⊤)
    {M : Type} [AddCommGroup M] {f g : W →+ M} (e : ∀ (c : F) v, f (c • a v) = g (c • a v)) (x : W) :
    f x = g x := by sorry
