-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_Unr_pow_eq_one_eq_of_residue
-- name    : GlobalTheory.UnitLemma.Unr.pow_eq_one_eq_of_residue
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T21:39:22.813945+00:00
-- url     : https://prove2.me/theorems/e03292bb-3b4d-4a5b-a103-4886eec8b3f5
-- title:
--   Unr: pow eq one eq of residue
-- statement:
--   The Unr construction uses the pow eq one eq of residue property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsUnramifiedInvolutionFieldEmbedding.lean#L16-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsUnramifiedInvolutionFieldEmbedding.lean#L16-L43

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OverExtAlgebraMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocalRingOfIdem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_FiniteMaximalSpectrumOfFiniteOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MonicDvdXPowCardSubOneExistsRootStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_InvolutionResiduePowAndRootsOfUnityStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsIntegralIntegersUnramifiedInvolutionExtStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AdjoinPrimitiveRootEqIntegersUnramifiedQuadraticStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsUnramifiedInvolutionFieldEmbedding
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr
open GlobalTheory.UnitLemma Polynomial IsLocalRing

theorem GlobalTheory.UnitLemma.Unr.pow_eq_one_eq_of_residue {S : Type*} [CommRing S] [IsLocalRing S] {n : ℕ} (hn : IsUnit (n : S))
    {y₁ y₂ : S} (h₁ : y₁ ^ n = 1) (h₂ : y₂ ^ n = 1) (h : residue S y₁ = residue S y₂) : y₁ = y₂ := by sorry
