-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_UnrAny_pow_eq_one_eq_of_residue
-- name    : GlobalTheory.UnitLemma.UnrAny.pow_eq_one_eq_of_residue
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T21:38:21.358502+00:00
-- url     : https://prove2.me/theorems/388295e5-7881-4d82-a84e-771c1ac800d5
-- title:
--   Unr Any: pow eq one eq of residue
-- statement:
--   The Unr Any construction uses the pow eq one eq of residue property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsUnramifiedEmbeddingOfInvolutionAlgebra.lean#L16-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsUnramifiedEmbeddingOfInvolutionAlgebra.lean#L16-L43

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OverExtAlgebraMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocalRingOfIdem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_FiniteMaximalSpectrumOfFiniteOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MonicDvdXPowCardSubOneExistsRootStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_InvolutionResiduePowAndRootsOfUnityStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsIntegralIntegersUnramifiedInvolutionExtStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AdjoinPrimitiveRootEqIntegersUnramifiedQuadraticStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsUnramifiedEmbeddingOfInvolutionAlgebra
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.UnrAny
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial IsLocalRing

theorem GlobalTheory.UnitLemma.UnrAny.pow_eq_one_eq_of_residue {S : Type*} [CommRing S] [IsLocalRing S] {n : ℕ} (hn : IsUnit (n : S))
    {y₁ y₂ : S} (h₁ : y₁ ^ n = 1) (h₂ : y₂ ^ n = 1) (h : residue S y₁ = residue S y₂) : y₁ = y₂ := by sorry
