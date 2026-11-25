-- Prove2me | Theorems.Thm_GlobalTheory_HeisLine_admitted_mono
-- name    : GlobalTheory.HeisLine.admitted.mono
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:07:35.906236+00:00
-- url     : https://prove2.me/theorems/453f3d36-8203-473e-b0f4-b62dbab0b610
-- title:
--   admitted: mono
-- statement:
--   The admitted construction uses the mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/AddCharDotProductTrivialOnTsupportNhds.lean#L204-L205
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/AddCharDotProductTrivialOnTsupportNhds.lean#L204-L205

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FourierTransformInversionLocalFieldPi
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_AddCharConductorAndHaarIntegersExist
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsCompactOpenAddSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_AddCharDotProductTrivialOnTsupportNhds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.SplitWeil MeasureTheory ValuativeRel Matrix
open scoped Topology
noncomputable section
open GlobalTheory GlobalTheory.HeisLine
open GlobalTheory.SplitWeil.FourierPi
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n : Type} [Fintype n]
variable [MeasurableSpace k] [BorelSpace k]
variable {χ : AddChar k Circle} {c : kˣ}
omit [MeasurableSpace k] [BorelSpace k]

theorem GlobalTheory.HeisLine.admitted.mono {s s' : kˣ} {g : (n → k) → ℂ} (h : admitted χ s g) (hs : box n s' ⊆ box n s) : admitted χ s' g := by sorry
