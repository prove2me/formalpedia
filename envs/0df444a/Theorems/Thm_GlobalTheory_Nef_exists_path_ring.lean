-- Prove2me | Theorems.Thm_GlobalTheory_Nef_exists_path_ring
-- name    : GlobalTheory.Nef.exists_path_ring
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T02:48:19.466805+00:00
-- url     : https://prove2.me/theorems/1780dacd-bb51-4edb-a422-24597233bfae
-- title:
--   Nef: exists path ring
-- statement:
--   The Nef construction uses the exists path ring property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsPathFormallySmoothRing.lean#L14-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsPathFormallySmoothRing.lean#L14-L27

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsAdmissibleIntegralBasisChangeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DerivCompM
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsDoublingJetOfOrderTwoFirstOrderStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsIsRingHomModXPowSuccLiftStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsDoublingJetSuccOfLiftStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsRingHomLimitOfDoublingJetsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsPathFormallySmoothRing
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef
open GlobalTheory GlobalTheory.Nef

theorem GlobalTheory.Nef.exists_path_ring : ∀ (A B R : Type) [CommRing A] [CommRing B] [CommRing R] [Algebra ℚ R] (π : B →+* A) (ε : A →+* B) (m : A →+* A) (β : B →+* R) (δ : A →+ R), π.FormallySmooth → ε.comp π = RingHom.id B → m.comp π = π → ε.comp m = ε → (∀ f ∈ RingHom.ker ε, m f - 2 * f ∈ RingHom.ker ε ^ 2) → (∀ f g, δ (f * g) = β (ε f) * δ g + β (ε g) * δ f) → (∀ a, δ (π a) = 0) → ∃ γ : A →+* PowerSeries R, γ.comp π = PowerSeries.C.comp β ∧ PowerSeries.constantCoeff.comp γ = β.comp ε ∧ (∀ f, PowerSeries.coeff 1 (γ f) = δ f) ∧ (PowerSeries.rescale 2).comp γ = γ.comp m := by sorry
