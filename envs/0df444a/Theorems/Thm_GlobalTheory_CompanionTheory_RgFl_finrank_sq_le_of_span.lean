-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgFl_finrank_sq_le_of_span
-- name    : GlobalTheory.CompanionTheory.RgFl.finrank_sq_le_of_span
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T11:59:49.043424+00:00
-- url     : https://prove2.me/theorems/ef82c252-d4f7-4f00-8d62-0e04fe24ae11
-- title:
--   Rg Fl: finrank sq le of span
-- statement:
--   The Rg Fl construction uses the finrank sq le of span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/SimpleOfCommutativeStatement.lean#L11-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/SimpleOfCommutativeStatement.lean#L11-L60

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_InhabitedFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_BurnsideSurjOfIrred
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_SimpleOfCommutativeStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CompanionTheory.Rg.Fl
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgFl

theorem GlobalTheory.CompanionTheory.RgFl.finrank_sq_le_of_span {A V : Type} [Ring A] [Algebra ℂ A] [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (ρ : A →ₐ[ℂ] Module.End ℂ V) (hρ : Function.Surjective ρ) {d l : ℕ}
    (x y : Fin d → A) (a : Fin l → A)
    (hs : Submodule.span ℂ {z | ∃ i j, ∃ c ∈ Algebra.adjoin ℂ (Set.range a), z = x i * c * y j} = ⊤) :
    Module.finrank ℂ V ^ 2 ≤
      d ^ 2 * Module.finrank ℂ (Algebra.adjoin ℂ (Set.range fun i => ρ (a i))) := by sorry
