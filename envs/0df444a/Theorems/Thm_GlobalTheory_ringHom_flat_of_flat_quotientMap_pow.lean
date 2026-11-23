-- Prove2me | Theorems.Thm_GlobalTheory_ringHom_flat_of_flat_quotientMap_pow
-- name    : GlobalTheory.ringHom_flat_of_flat_quotientMap_pow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:56:21.814544+00:00
-- url     : https://prove2.me/theorems/fbd778df-dc6d-4cc6-a736-97738a1cc85f
-- title:
--   Global Theory: ring Hom flat of flat quotient Map pow
-- statement:
--   The Global Theory construction uses the ring Hom flat of flat quotient Map pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IdealEqBotOfFlatQuotientOfMapMaximalIdeal.lean#L204-L213
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IdealEqBotOfFlatQuotientOfMapMaximalIdeal.lean#L204-L213

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueFactorCompletedStalkOfMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsMemPowSubMemPowSucc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IdealEqBotOfFlatQuotientOfMapMaximalIdeal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct LinearMap
open GlobalTheory
universe u v w
open IsLocalRing
variable {A B : Type*} [CommRing A] [CommRing B] [IsNoetherianRing A] [IsNoetherianRing B]

theorem GlobalTheory.ringHom_flat_of_flat_quotientMap_pow (φ : A →+* B) {I : Ideal A} {J : Ideal B}
    (hIJ : I.map φ = J) (hJ : J ≤ Ideal.jacobson ⊥) (hle : ∀ n : ℕ, I ^ n ≤ (J ^ n).comap φ)
    (h : ∀ n : ℕ, (Ideal.quotientMap (J ^ n) φ (hle n)).Flat) : φ.Flat := by sorry
