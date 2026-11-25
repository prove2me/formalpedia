-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_OmegaColumnSlices_hat_mem_SB_and_hat_omCol
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.OmegaColumnSlices.hat_mem_SB_and_hat_omCol
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:09:41.384808+00:00
-- url     : https://prove2.me/theorems/d3c5bbdb-6657-4799-80b9-eba9e33ff358
-- title:
--   Omega Column Slices: hat mem SB and hat om Col
-- statement:
--   The Omega Column Slices construction uses the hat mem SB and hat om Col property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/HatMemSBAndHatOmCol.lean#L10-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/HatMemSBAndHatOmCol.lean#L10-L41

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_OmegaColumnSlices
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_TypeChainPrincipalEntryNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LinearChangeOfVariablesLocalFieldMatrix
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FourierTransformInversionLocalFieldPi
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HatMemSBAndHatOmCol
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.OmegaColumnSlices
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.OmegaColumnSlices

theorem GlobalTheory.IndefiniteRowSideFullHecke.OmegaColumnSlices.hat_mem_SB_and_hat_omCol : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k) (ε : k), HasConductor ψ 1 → IsUnitVol ν → valuation k ε = 1 → ∀ (n : Type) [Fintype n] [DecidableEq n] (μz : kˣ →* ℂˣ) (h : GL n k), ∀ φ ∈ SB (n → k), hat ψ ν ε φ ∈ SB (n → k) ∧ hat ψ ν ε (omCol μz h φ) = omRow μz h (hat ψ ν ε φ) := by sorry
