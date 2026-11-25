-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_CongruenceCayley_inv_small
-- name    : GlobalTheory.UnitLemma.CongruenceCayley.inv_small
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T01:05:40.802042+00:00
-- url     : https://prove2.me/theorems/134946f3-c59e-446c-bb95-eaeb5303a627
-- title:
--   Congruence Cayley: inv small
-- statement:
--   The Congruence Cayley construction uses the inv small property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IdentityOfPrincipalCongruence.lean#L15-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IdentityOfPrincipalCongruence.lean#L15-L51

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

theorem GlobalTheory.UnitLemma.CongruenceCayley.inv_small {O A : Type} [CommRing O] [IsLocalRing O] [CommRing A] [Algebra O A] (g : A) (α β : O)
    (hg : IsIntegral O g) (hα : IsUnit α) (hβ : β ∈ IsLocalRing.maximalIdeal O) :
    ∃ w ∈ Algebra.adjoin O ({g} : Set A), (algebraMap O A α + algebraMap O A β * g) * w = 1 := by sorry
