-- Prove2me | Theorems.Thm_GlobalTheory_IdealChain_monLat_congr
-- name    : GlobalTheory.IdealChain.monLat_congr
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:07:38.920545+00:00
-- url     : https://prove2.me/theorems/92216a14-5383-44f3-90d4-5eba4834ab7f
-- title:
--   Ideal Chain: mon Lat congr
-- statement:
--   The Ideal Chain construction uses the mon Lat congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/NabsDetEqOfActEq.lean#L55-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/NabsDetEqOfActEq.lean#L55-L59

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
omit [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem GlobalTheory.IdealChain.monLat_congr {n : Type} {c : ℕ} (L : Submodule 𝒪[k] (n → k)) {b b' : ℕ → kˣ}
    (h : ∀ i, 1 ≤ i → i ≤ c → idl (b i) = idl (b' i)) : monLat c L b = monLat c L b' := by sorry
