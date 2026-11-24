-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_UnitBase_maximal_finite
-- name    : GlobalTheory.UnitLemma.UnitBase.maximal_finite
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T21:34:28.223627+00:00
-- url     : https://prove2.me/theorems/cefc4c4f-2a28-4bb7-8024-8ef85324c094
-- title:
--   Unit Base: maximal finite
-- statement:
--   The Unit Base construction uses the maximal finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsUnitBasePointAdjoinTwistedSigma.lean#L158-L166
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsUnitBasePointAdjoinTwistedSigma.lean#L158-L166

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsUnitBasePointAdjoinTwistedSigma
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.UnitBase
open GlobalTheory.UnitLemma Polynomial

theorem GlobalTheory.UnitLemma.UnitBase.maximal_finite {K : UQ} (B : InvAlg K) (hint : IsIntegral K.O B.g) :
    {M : Ideal (Algebra.adjoin K.O {B.g}) | M.IsMaximal}.Finite := by sorry
