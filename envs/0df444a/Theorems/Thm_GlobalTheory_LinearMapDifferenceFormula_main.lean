-- Prove2me | Theorems.Thm_GlobalTheory_LinearMapDifferenceFormula_main
-- name    : GlobalTheory.LinearMapDifferenceFormula.main
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T18:11:03.56404+00:00
-- url     : https://prove2.me/theorems/ad13a68b-a9b0-495f-b531-68445da3c535
-- title:
--   Linear Map Difference Formula: main
-- statement:
--   The Linear Map Difference Formula construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MapSubApply.lean#L15-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MapSubApply.lean#L15-L62

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MapSubApply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.LinearMapDifferenceFormula
open AdicCompletion

theorem GlobalTheory.LinearMapDifferenceFormula.main : ∀ (A : Type) [inst : CommRing A] [IsNoetherianRing A] (J : Ideal A) (N M : Type) [inst_2 : AddCommGroup N] [inst_3 : Module A N] [inst_4 : AddCommGroup M] [inst_5 : Module A M] [Module.Finite A M] (f : N →ₗ[A] M) (Γ : Type) [Finite Γ] (g : Γ → M →ₗ[A] M), Function.Injective (⇑f : N → M) → (∀ (x : M), x ∈ LinearMap.range f ↔ ∀ (σ : Γ), (g σ : M → M) x = x) → Function.Injective (⇑(AdicCompletion.map J f) : AdicCompletion J N → AdicCompletion J M) ∧ ∀ (y : AdicCompletion J M), y ∈ LinearMap.range (AdicCompletion.map J f) ↔ ∀ (σ : Γ), (AdicCompletion.map J (g σ) : AdicCompletion J M → AdicCompletion J M) y = y := by sorry
