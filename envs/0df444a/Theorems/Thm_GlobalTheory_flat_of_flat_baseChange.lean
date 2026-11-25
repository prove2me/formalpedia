-- Prove2me | Theorems.Thm_GlobalTheory_flat_of_flat_baseChange
-- name    : GlobalTheory.flat_of_flat_baseChange
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T22:52:18.685373+00:00
-- url     : https://prove2.me/theorems/6c1f5714-5345-44d6-8806-d570a5cbc704
-- title:
--   Global Theory: flat of flat base Change
-- statement:
--   The Global Theory construction uses the flat of flat base Change property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IdealEqBotOfFlatQuotientOfMapMaximalIdeal.lean#L497-L502
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IdealEqBotOfFlatQuotientOfMapMaximalIdeal.lean#L497-L502

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
variable {A B A' B' : Type*} [CommRing A] [CommRing B] [CommRing A'] [CommRing B']

theorem GlobalTheory.flat_of_flat_baseChange {k : Type*} (K : Type*) [CommRing k] [CommRing K] [Algebra k K]
    [Module.FaithfullyFlat k K] [Algebra k A] [Algebra k B] (φ : A →ₐ[k] B)
    (h : (Algebra.TensorProduct.map (AlgHom.id k K) φ : K ⊗[k] A →+* K ⊗[k] B).Flat) :
    (φ : A →+* B).Flat := by sorry
