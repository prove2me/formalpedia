-- Prove2me | Theorems.Thm_GlobalTheory_AugCot_map_comp
-- name    : GlobalTheory.AugCot.map_comp
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T11:46:24.735118+00:00
-- url     : https://prove2.me/theorems/a3a171b5-1649-41d7-8344-910afdca8127
-- title:
--   Aug Cot: map comp
-- statement:
--   The Aug Cot construction uses the map comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/FinrankOfIsStandardSmoothOfRelativeDimension.lean#L301-L304
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/FinrankOfIsStandardSmoothOfRelativeDimension.lean#L301-L304

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FinrankOfIsStandardSmoothOfRelativeDimension
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
noncomputable section
open GlobalTheory
open GlobalTheory.AugCot
variable {R A B C : Type*} [CommRing R] [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]
  [CommRing C] [Algebra R C] {εA : A →ₐ[R] R} {εB : B →ₐ[R] R} {εC : C →ₐ[R] R}

theorem GlobalTheory.AugCot.map_comp (φ : A →ₐ[R] B) (ψ : B →ₐ[R] C) (h : εB.comp φ = εA) (h' : εC.comp ψ = εB)
    (h'' : εC.comp (ψ.comp φ) = εA := by rw [← AlgHom.comp_assoc, h', h]) :
    map (ψ.comp φ) h'' = map ψ h' ∘ₗ map φ h := by sorry
