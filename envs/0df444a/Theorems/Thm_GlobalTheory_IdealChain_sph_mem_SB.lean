-- Prove2me | Theorems.Thm_GlobalTheory_IdealChain_sph_mem_SB
-- name    : GlobalTheory.IdealChain.sph_mem_SB
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:08:28.30385+00:00
-- url     : https://prove2.me/theorems/be89ec3e-33fc-428d-a562-703d69fa1f41
-- title:
--   Ideal Chain: sph mem SB
-- statement:
--   The Ideal Chain construction uses the sph mem SB property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/NabsDetEqOfActEq.lean#L148-L158
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/NabsDetEqOfActEq.lean#L148-L158

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_HalfPowerSpherical
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsClopenIsCompactMapsPair
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormalizedAbsCharacterization
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IntegralCompBlocks
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ValuationDetOfMemKO
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NabsDetEqOfActEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.HalfPowerSpherical GlobalTheory.LatPair GlobalTheory.StepData
open scoped Pointwise
noncomputable section
open GlobalTheory GlobalTheory.IdealChain
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {ι ι' : Type} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']
omit [DecidableEq ι] [DecidableEq ι']

theorem GlobalTheory.IdealChain.sph_mem_SB (α : kˣ) {L' : Submodule 𝒪[k] (ι' → k)} {L : Submodule 𝒪[k] (ι → k)} (h' : L'.IsLattice k)
    (h : L.IsLattice k) : sph α L' L ∈ SB (Matrix ι ι' k) := by sorry
