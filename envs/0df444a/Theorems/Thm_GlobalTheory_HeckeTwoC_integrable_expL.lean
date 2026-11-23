-- Prove2me | Theorems.Thm_GlobalTheory_HeckeTwoC_integrable_expL
-- name    : GlobalTheory.HeckeTwoC.integrable_expL
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:04:33.329047+00:00
-- url     : https://prove2.me/theorems/b3daec91-b064-4f9b-8ca8-d04c230e6e26
-- title:
--   Hecke Two C: integrable exp L
-- statement:
--   The Hecke Two C construction uses the integrable exp L property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HeckePhiFourierConstantAtZeroDifferentiableOn.lean#L92-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HeckePhiFourierConstantAtZeroDifferentiableOn.lean#L92-L97

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckePhiFourierConstantAtZeroDifferentiableOn
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
open GlobalTheory GlobalTheory.HeckeTwoC
open MeasureTheory

theorem GlobalTheory.HeckeTwoC.integrable_expL {ε : ℝ} (hε : 0 < ε) : Integrable (fun t : ℝ => Real.exp (-(1 + ε) * lg t)) := by sorry
