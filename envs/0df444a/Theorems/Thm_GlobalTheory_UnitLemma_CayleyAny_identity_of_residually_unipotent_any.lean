-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_CayleyAny_identity_of_residually_unipotent_any
-- name    : GlobalTheory.UnitLemma.CayleyAny.identity_of_residually_unipotent_any
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T01:02:14.694771+00:00
-- url     : https://prove2.me/theorems/a20cc58d-d431-482b-937c-f5a023efc295
-- title:
--   Cayley Any: identity of residually unipotent any
-- statement:
--   The Cayley Any construction uses the identity of residually unipotent any property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UnitLemmaResiduallyUnipotentCayleyTransform.lean#L107-L223
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UnitLemmaResiduallyUnipotentCayleyTransform.lean#L107-L223

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitLemmaResiduallyUnipotentViaCayley
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitLemmaResiduallyUnipotentCayleyTransform
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.UnitLemma Polynomial
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.CayleyAny
open GlobalTheory.UnitLemma.CayleyCase

theorem GlobalTheory.UnitLemma.CayleyAny.identity_of_residually_unipotent_any : UnitLemmaLie → ∀ (K : UQ) (B₁ B₂ : InvAlg K),
    B₁.g * B₁.σ B₁.g = 1 → B₂.g * B₂.σ B₂.g = 1 → (B₁.P * B₂.P).Separable → ∀ s : K.Oˣ,
    algebraMap K.O K.E s * K.c (algebraMap K.O K.E s) = 1 →
    (∃ Q : K.O[X], Q.map (algebraMap K.O K.E) = B₁.P * B₂.P ∧
      Q.map (IsLocalRing.residue K.O) = (X - C (IsLocalRing.residue K.O s)) ^ Q.natDegree) →
    InvAlg.Identity B₁ B₂ := by sorry
