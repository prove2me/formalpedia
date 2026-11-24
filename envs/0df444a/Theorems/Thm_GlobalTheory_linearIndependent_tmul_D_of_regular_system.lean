-- Prove2me | Theorems.Thm_GlobalTheory_linearIndependent_tmul_D_of_regular_system
-- name    : GlobalTheory.linearIndependent_tmul_D_of_regular_system
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T23:07:28.910856+00:00
-- url     : https://prove2.me/theorems/381ce38b-ccd9-4003-8d97-fcce2f2bbb7c
-- title:
--   Global Theory: linear Independent tmul D of regular system
-- statement:
--   The Global Theory construction uses the linear Independent tmul D of regular system property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RegularLocalDifferentialsBasis.lean#L10-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RegularLocalDifferentialsBasis.lean#L10-L48

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemSqLocalizationOfPderivMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsMinimalLocalGenerators
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RegularLocalDifferentialsBasis
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct Polynomial
open IsLocalRing TensorProduct
open GlobalTheory

theorem GlobalTheory.linearIndependent_tmul_D_of_regular_system :
    ∀ (k A : Type) [Field k] [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [Algebra k A] [Algebra.FormallySmooth k (IsLocalRing.ResidueField A)] (n : ℕ) (t : Fin n → A), Ideal.span (Set.range t) = IsLocalRing.maximalIdeal A → (n : WithBot ℕ∞) = ringKrullDim A → LinearIndependent (IsLocalRing.ResidueField A) (fun a => (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] KaehlerDifferential.D k A (t a)) := by sorry
