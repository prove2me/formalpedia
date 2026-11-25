-- Prove2me | Theorems.Thm_GlobalTheory_DI_FrobeniusTwistSmul_main
-- name    : GlobalTheory.DI.FrobeniusTwistSmul.main
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:03:16.263616+00:00
-- url     : https://prove2.me/theorems/2f2355db-82e8-5fb7-87ef-2a0d559c2b73
-- title:
--   Frobenius Twist Smul: main
-- statement:
--   The Frobenius Twist Smul construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsExteriorAlgebraExtensionOfFrobeniusSemilin.lean#L22-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsExteriorAlgebraExtensionOfFrobeniusSemilin.lean#L22-L37

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFlatLift
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsExteriorAlgebraExtensionOfFrobeniusSemilin
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.DI
open GlobalTheory GlobalTheory.DI GlobalTheory.DI.FrobeniusTwistSmul

theorem GlobalTheory.DI.FrobeniusTwistSmul.main : ∀ {K : Type} [CommRing K] {V : Type} [AddCommGroup V] [Module K V] {W : Type} [AddCommGroup W] [Module K W] (p : ℕ) [Fact p.Prime] [CharP K p] (g : ∀ a : ℕ, (Fin a → V) → W), (∀ a v k x y, g a (Function.update v k (x + y)) = g a (Function.update v k x) + g a (Function.update v k y)) → (∀ a v k (c : K) x, g a (Function.update v k (c • x)) = c ^ p • g a (Function.update v k x)) → (∀ a v k l, k ≠ l → v k = v l → g a v = 0) → ∃ Φ : ExteriorAlgebra K V →+ W, ∀ (c : K) (a : ℕ) (v : Fin a → V), Φ (c • ExteriorAlgebra.ιMulti K a v) = c ^ p • g a v := by sorry
