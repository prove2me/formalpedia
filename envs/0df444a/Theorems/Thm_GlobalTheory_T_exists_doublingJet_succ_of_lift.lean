-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_doublingJet_succ_of_lift
-- name    : GlobalTheory.T.exists_doublingJet_succ_of_lift
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T01:13:17.60149+00:00
-- url     : https://prove2.me/theorems/32dab883-c050-407e-b77e-329cb7befad1
-- title:
--   T: exists doubling Jet succ of lift
-- statement:
--   The T construction uses the exists doubling Jet succ of lift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsDoublingJetSuccOfLiftStatement.lean#L9-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsDoublingJetSuccOfLiftStatement.lean#L9-L10

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsDoublingJetSuccOfLift
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DerivCompM
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsDoublingJetSuccOfLiftStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.Nef
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_doublingJet_succ_of_lift : ∀ (A B R : Type) [CommRing A] [CommRing B] [CommRing R] [Algebra ℚ R] (π : B →+* A) (ε : A →+* B) (m : A →+* A) (β : B →+* R) (δ : A →+ R), ε.comp π = RingHom.id B → m.comp π = π → ε.comp m = ε → (∀ f ∈ RingHom.ker ε, m f - 2 * f ∈ RingHom.ker ε ^ 2) → (∀ f g, δ (f * g) = β (ε f) * δ g + β (ε g) * δ f) → (∀ a, δ (π a) = 0) → ∀ n : ℕ, 2 ≤ n → ∀ φ ψ : A → PowerSeries R, GlobalTheory.Nef.PathJet.IsJet π ε m β δ n φ → GlobalTheory.Nef.PathJet.IsRingHomMod π β (n + 1) ψ → (∀ f, (PowerSeries.X : PowerSeries R) ^ n ∣ ψ f - φ f) → ∃ ψ' : A → PowerSeries R, GlobalTheory.Nef.PathJet.IsJet π ε m β δ (n + 1) ψ' ∧ ∀ f, (PowerSeries.X : PowerSeries R) ^ n ∣ ψ' f - φ f := by sorry
