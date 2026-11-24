-- Prove2me | Theorems.Thm_GlobalTheory_HeckeTwoUnit_phi_smul
-- name    : GlobalTheory.HeckeTwoUnit.phi_smul
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T14:15:56.436053+00:00
-- url     : https://prove2.me/theorems/153aa89e-020d-40c3-91a1-a41ed264246e
-- title:
--   Hecke Two Unit: phi smul
-- statement:
--   The Hecke Two Unit construction uses the phi smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HeckeEisensteinFourierTermMoveUnit.lean#L13-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HeckeEisensteinFourierTermMoveUnit.lean#L13-L18

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AbsNormEqProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeEisensteinFourierTermMoveUnit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo
noncomputable section
open GlobalTheory GlobalTheory.HeckeTwoUnit

theorem GlobalTheory.HeckeTwoUnit.phi_smul (σ : ℂ) {l : ℝ} (hl : l ≠ 0) (w : ℂ) :
    phi σ ((l : ℂ) * w) = ((l : ℂ)⁻¹ ^ 2 * ((|l| : ℝ) : ℂ) ^ (-2 * σ)) * phi σ w := by sorry
