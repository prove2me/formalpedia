-- Prove2me | Theorems.Thm_GlobalTheory_torsion_gens_glue_of_local
-- name    : GlobalTheory.torsion_gens_glue_of_local
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:23:48.047194+00:00
-- url     : https://prove2.me/theorems/de505b3f-e92a-45aa-aba7-538aff95af9c
-- title:
--   Global Theory: torsion gens glue of local
-- statement:
--   The Global Theory construction uses the torsion gens glue of local property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/TorsionTwoGeneratorsGlobal.lean#L6-L146
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/TorsionTwoGeneratorsGlobal.lean#L6-L146

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TorsionTwoGeneratorsGlobal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open GlobalTheory

theorem GlobalTheory.torsion_gens_glue_of_local (F : Type) [Field F] [NumberField F] (M : Type) [AddCommGroup M]
    [Module (𝓞 F) M] (N : ℕ) (hN : 1 ≤ N) (hfin : Finite {x : M // N • x = 0})
    (H : ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal → (N : 𝓞 F) ∈ 𝔭 →
      ∃ u v : M, N • u = 0 ∧ N • v = 0 ∧ ∀ x : M, N • x = 0 → ∃ a b : 𝓞 F,
        x - a • u - b • v ∈ 𝔭 • Submodule.torsionBy (𝓞 F) M (N : 𝓞 F)) :
    ∃ p : Fin 2 → M, (∀ i, N • p i = 0) ∧ ∀ y : M, N • y = 0 → ∃ a b : 𝓞 F, y = a • p 0 + b • p 1 := by sorry
