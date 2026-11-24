-- Prove2me | Theorems.Thm_GlobalTheory_surjective_injective_of_fibre_rank
-- name    : GlobalTheory.surjective_injective_of_fibre_rank
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T11:52:01.477083+00:00
-- url     : https://prove2.me/theorems/9f31b9be-3ec1-4491-99b7-a8f750491eec
-- title:
--   Global Theory: surjective injective of fibre rank
-- statement:
--   The Global Theory construction uses the surjective injective of fibre rank property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SubsingletonOfResidueFieldFibres.lean#L70-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SubsingletonOfResidueFieldFibres.lean#L70-L74

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SubsingletonOfResidueFieldFibres
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open TensorProduct

theorem GlobalTheory.surjective_injective_of_fibre_rank :
    ∀ (O M N : Type) [CommRing O] [AddCommGroup M] [Module O M] [AddCommGroup N] [Module O N] [Module.Finite O N] (f : M →ₗ[O] N), ((∀ q : PrimeSpectrum O, Module.finrank q.asIdeal.ResidueField (LinearMap.range (f.baseChange q.asIdeal.ResidueField)) = Module.finrank q.asIdeal.ResidueField (TensorProduct O q.asIdeal.ResidueField N)) → Function.Surjective f) ∧ (Module.Finite O M → Module.Projective O N → Function.Surjective f → (∀ q : PrimeSpectrum O, Module.finrank q.asIdeal.ResidueField (TensorProduct O q.asIdeal.ResidueField M) = Module.finrank q.asIdeal.ResidueField (TensorProduct O q.asIdeal.ResidueField N)) → Function.Injective f) := by sorry
