-- Prove2me | Theorems.Thm_GlobalTheory_SCV_eqOn_of_eqOn_open
-- name    : GlobalTheory.SCV.eqOn_of_eqOn_open
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:57:33.358088+00:00
-- url     : https://prove2.me/theorems/06e7be11-56ab-4932-bd3f-bfe4644f6ef4
-- title:
--   SCV: eq On of eq On open
-- statement:
--   The SCV construction uses the eq On of eq On open property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/DifferentiableOnOfTendstoLocallyUniformlyOn.lean#L331-L336
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/DifferentiableOnOfTendstoLocallyUniformlyOn.lean#L331-L336

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Metric Set Filter
open scoped Topology ContDiff Nat
open GlobalTheory GlobalTheory.SCV
variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]

theorem GlobalTheory.SCV.eqOn_of_eqOn_open {f g : E → V} {U W : Set E} (hU : IsOpen U) (hU' : IsPreconnected U)
    (hf : DifferentiableOn ℂ f U) (hg : DifferentiableOn ℂ g U) (hW : IsOpen W)
    (hne : W.Nonempty) (hWU : W ⊆ U) (hfg : EqOn f g W) : EqOn f g U := by sorry
