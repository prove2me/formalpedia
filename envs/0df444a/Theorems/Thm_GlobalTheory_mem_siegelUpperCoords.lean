-- Prove2me | Theorems.Thm_GlobalTheory_mem_siegelUpperCoords
-- name    : GlobalTheory.mem_siegelUpperCoords
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:56:15.745875+00:00
-- url     : https://prove2.me/theorems/f0461748-6920-4d4f-b924-72f7c41fa109
-- title:
--   Global Theory: mem siegel Upper Coords
-- statement:
--   The Global Theory construction uses the mem siegel Upper Coords property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/HasSumLocallyUniformlyOnIteratedFDerivRiemannThe.lean#L94-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/HasSumLocallyUniformlyOnIteratedFDerivRiemannThe.lean#L94-L95

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
variable {ι : Type*} [LinearOrder ι]

theorem GlobalTheory.mem_siegelUpperCoords {x : {p : ι × ι // p.1 ≤ p.2} → ℂ} :
    x ∈ siegelUpperCoords ι ↔ IsSiegel (symmOfUpper x) := by sorry
