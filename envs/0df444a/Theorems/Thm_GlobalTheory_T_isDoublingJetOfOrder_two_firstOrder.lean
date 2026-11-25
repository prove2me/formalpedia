-- Prove2me | Theorems.Thm_GlobalTheory_T_isDoublingJetOfOrder_two_firstOrder
-- name    : GlobalTheory.T.isDoublingJetOfOrder_two_firstOrder
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T01:14:50.0208+00:00
-- url     : https://prove2.me/theorems/5cea7085-66dc-4db7-ba82-f15e5bcc501a
-- title:
--   T: is Doubling Jet Of Order two first Order
-- statement:
--   The T construction uses the is Doubling Jet Of Order two first Order property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsDoublingJetOfOrderTwoFirstOrderStatement.lean#L9-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsDoublingJetOfOrderTwoFirstOrderStatement.lean#L9-L10

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsDoublingJetOfOrderTwoFirstOrder
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DerivCompM
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsDoublingJetOfOrderTwoFirstOrderStatement
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

theorem GlobalTheory.T.isDoublingJetOfOrder_two_firstOrder : ∀ (A B R : Type) [CommRing A] [CommRing B] [CommRing R] (π : B →+* A) (ε : A →+* B) (m : A →+* A) (β : B →+* R) (δ : A →+ R), ε.comp π = RingHom.id B → m.comp π = π → ε.comp m = ε → (∀ f ∈ RingHom.ker ε, m f - 2 * f ∈ RingHom.ker ε ^ 2) → (∀ f g, δ (f * g) = β (ε f) * δ g + β (ε g) * δ f) → (∀ a, δ (π a) = 0) → GlobalTheory.Nef.PathJet.IsJet π ε m β δ 2 (fun f => PowerSeries.C (β (ε f)) + PowerSeries.C (δ f) * PowerSeries.X) := by sorry
