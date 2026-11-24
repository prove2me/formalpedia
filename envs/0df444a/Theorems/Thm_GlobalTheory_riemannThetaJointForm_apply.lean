-- Prove2me | Theorems.Thm_GlobalTheory_riemannThetaJointForm_apply
-- name    : GlobalTheory.riemannThetaJointForm_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:56:29.813481+00:00
-- url     : https://prove2.me/theorems/11ec501e-1327-4c4f-abcd-02100b64c47b
-- title:
--   Global Theory: riemann Theta Joint Form apply
-- statement:
--   The Global Theory construction uses the riemann Theta Joint Form apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/HasSumLocallyUniformlyOnIteratedFDerivRiemannThe.lean#L20-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/HasSumLocallyUniformlyOnIteratedFDerivRiemannThe.lean#L20-L33

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsEventuallyNormRiemannThetaTermLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LineDerivListEqIteratedFDeriv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_HasSumLocallyUniformlyOnIteratedFDerivRiemannThe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix Filter Topology
open scoped Real
noncomputable section
open GlobalTheory
variable {ι : Type*} [Fintype ι]

theorem GlobalTheory.riemannThetaJointForm_apply (a : ι → ℝ) (n : ι → ℤ)
    (p : (ι → ℂ) × (ι → ι → ℂ)) :
    riemannThetaJointForm a n p =
      2 * π * I * (((fun i => (n i : ℂ) + a i) ⬝ᵥ (of p.2 *ᵥ fun i => (n i : ℂ) + a i)) / 2 +
        (fun i => (n i : ℂ) + a i) ⬝ᵥ p.1) := by sorry
