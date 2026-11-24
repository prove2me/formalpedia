-- Prove2me | Theorems.Thm_GlobalTheory_IwahoriInj_exists_deep
-- name    : GlobalTheory.IwahoriInj.exists_deep
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:11:24.026259+00:00
-- url     : https://prove2.me/theorems/7c414feb-5e37-4151-83dd-d5bf80c64526
-- title:
--   Iwahori Inj: exists deep
-- statement:
--   The Iwahori Inj construction uses the exists deep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsLocallyConstantOrbit.lean#L145-L150
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsLocallyConstantOrbit.lean#L145-L150

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_TwistedKernelFixed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsLocallyConstantOrbit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel MeasureTheory
open GlobalTheory GlobalTheory.IwahoriInj
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem GlobalTheory.IwahoriInj.exists_deep (a : ℤ) : ∃ c : k, c ≠ 0 ∧ Deep a c ∧ Deep (-a) c⁻¹ := by sorry
