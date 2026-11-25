-- Prove2me | Theorems.Thm_GlobalTheory_T_torsion_two_generators_global
-- name    : GlobalTheory.T.torsion_two_generators_global
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:40:19.786124+00:00
-- url     : https://prove2.me/theorems/49c1f2c8-bad2-4e72-8f0c-573652960ce5
-- title:
--   T: torsion two generators global
-- statement:
--   The T construction uses the torsion two generators global property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/TorsionTwoGeneratorsGlobalStatement.lean#L6-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/TorsionTwoGeneratorsGlobalStatement.lean#L6-L11

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TorsionTwoGeneratorsGlobal
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TorsionTwoGeneratorsGlobalStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.torsion_two_generators_global : ∀ (F : Type) [Field F] [NumberField F] (M : Type) [AddCommGroup M] [Module (𝓞 F) M] (N : ℕ), 1 ≤ N → Finite {x : M // N • x = 0} →
    (∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal → (N : 𝓞 F) ∈ 𝔭 →
      ∃ u v : M, N • u = 0 ∧ N • v = 0 ∧ ∀ x : M, N • x = 0 → ∃ a b : 𝓞 F,
        x - a • u - b • v ∈ 𝔭 • Submodule.torsionBy (𝓞 F) M (N : 𝓞 F)) →
    ∃ p : Fin 2 → M, (∀ i, N • p i = 0) ∧ ∀ y : M, N • y = 0 → ∃ a b : 𝓞 F, y = a • p 0 + b • p 1 := by sorry
