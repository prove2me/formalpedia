-- Prove2me | Theorems.Thm_GlobalTheory_WeilM_nonarch_pi
-- name    : GlobalTheory.WeilM.nonarch_pi
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T03:56:42.310485+00:00
-- url     : https://prove2.me/theorems/5a3abe13-8c35-4caa-a4a3-e767469bd700
-- title:
--   Weil M: nonarch pi
-- statement:
--   The Weil M construction uses the nonarch pi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsLocallyConstantAddChar.lean#L91-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsLocallyConstantAddChar.lean#L91-L98

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormPowTwoPowSubOneGe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsLocallyConstantAddChar
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix ValuativeRel
open scoped NNReal Topology Pointwise
open GlobalTheory GlobalTheory.WeilM
variable (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem GlobalTheory.WeilM.nonarch_pi (κ : Type) [Fintype κ] : NonarchimedeanAddGroup (κ → F) := by sorry
