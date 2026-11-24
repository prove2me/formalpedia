-- Prove2me | Theorems.Thm_GlobalTheory_nonempty_adjoin_ringHom_zmod_of_dvd_eval
-- name    : GlobalTheory.nonempty_adjoin_ringHom_zmod_of_dvd_eval
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T23:12:18.77205+00:00
-- url     : https://prove2.me/theorems/90fa5043-f198-4eaf-a6d8-72b4ad2e0045
-- title:
--   Global Theory: nonempty adjoin ring Hom zmod of dvd eval
-- statement:
--   The Global Theory construction uses the nonempty adjoin ring Hom zmod of dvd eval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NumberFieldToModPSquared.lean#L59-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NumberFieldToModPSquared.lean#L59-L64

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SepIntPolyRootModPrimeSqStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NumberFieldToModPSquared
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct Polynomial
open GlobalTheory

theorem GlobalTheory.nonempty_adjoin_ringHom_zmod_of_dvd_eval : ∀ (K : Type) [Field K] [NumberField K] (θ : K), IsIntegral ℤ θ → ∀ (m : ℕ) (x : ℤ), (m : ℤ) ∣ (minpoly ℤ θ).eval x → Nonempty (Algebra.adjoin ℤ ({θ} : Set K) →+* ZMod m) := by sorry
