-- Prove2me | Theorems.Thm_GlobalTheory_exists_arithFrobenius_absGalois
-- name    : GlobalTheory.exists_arithFrobenius_absGalois
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:44:25.945961+00:00
-- url     : https://prove2.me/theorems/381773c7-662a-4298-bcc8-158a06f08077
-- title:
--   Global Theory: exists arith Frobenius abs Galois
-- statement:
--   The Global Theory construction uses the exists arith Frobenius abs Galois property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsArithFrobeniusAbsGalois.lean#L9-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsArithFrobeniusAbsGalois.lean#L9-L54

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsArithFrobeniusAbsGalois
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open IsLocalRing
open IsLocalRing

theorem GlobalTheory.exists_arithFrobenius_absGalois (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K] (hfin : Finite (IsLocalRing.ResidueField V)) (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] [Algebra V Ω] [IsScalarTower V K Ω] [IsLocalRing (integralClosure V Ω)] : ∃ φ : Ω ≃ₐ[K] Ω, ∀ x : integralClosure V Ω, ∃ y : integralClosure V Ω, (y : Ω) = φ x ∧ y - x ^ Nat.card (IsLocalRing.ResidueField V) ∈ IsLocalRing.maximalIdeal (integralClosure V Ω) := by sorry
