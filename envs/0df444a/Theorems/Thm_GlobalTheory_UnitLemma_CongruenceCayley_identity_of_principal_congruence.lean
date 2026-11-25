-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_CongruenceCayley_identity_of_principal_congruence
-- name    : GlobalTheory.UnitLemma.CongruenceCayley.identity_of_principal_congruence
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T01:04:56.029335+00:00
-- url     : https://prove2.me/theorems/f017f699-3e91-4582-8bad-3d50c5d8d912
-- title:
--   Congruence Cayley: identity of principal congruence
-- statement:
--   The Congruence Cayley construction uses the identity of principal congruence property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IdentityOfPrincipalCongruence.lean#L115-L185
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IdentityOfPrincipalCongruence.lean#L115-L185

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_KappaSumZeroAndStableSumMulZeroOfNotIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitLemmaResiduallyUnipotentViaCayley
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitLemmaResiduallyUnipotentCayleyTransform
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IdentityOfPrincipalCongruence
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
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.CongruenceCayley
open GlobalTheory.UnitLemma.CayleyCase

theorem GlobalTheory.UnitLemma.CongruenceCayley.identity_of_principal_congruence : UnitLemmaLie → ∀ (K : UQ) (a : K.O), K.Small a →
    ∀ B₁ B₂ : InvAlg K,
    (1 + algebraMap K.O B₁.A a * B₁.g) * B₁.σ (1 + algebraMap K.O B₁.A a * B₁.g) = 1 →
    (1 + algebraMap K.O B₂.A a * B₂.g) * B₂.σ (1 + algebraMap K.O B₂.A a * B₂.g) = 1 →
    (B₁.P * B₂.P).Separable → InvAlg.Identity B₁ B₂ := by sorry
