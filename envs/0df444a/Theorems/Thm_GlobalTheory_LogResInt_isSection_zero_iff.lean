-- Prove2me | Theorems.Thm_GlobalTheory_LogResInt_isSection_zero_iff
-- name    : GlobalTheory.LogResInt.isSection_zero_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:57:48.993817+00:00
-- url     : https://prove2.me/theorems/cb724faa-e55a-47c2-92a6-f5bf984cad57
-- title:
--   Log Res Int: is Section zero iff
-- statement:
--   The Log Res Int construction uses the is Section zero iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsClosedOfIsAnalyticSubset.lean#L69-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsClosedOfIsAnalyticSubset.lean#L69-L78

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AnalyticLogResolution
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsClosedOfIsAnalyticSubset
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.LogResInt
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.IndefiniteRowSideFullHecke.BoundaryPolynomialFunctions
noncomputable section
variable {d : ℕ} {X : Type} [TopologicalSpace X]

theorem GlobalTheory.LogResInt.isSection_zero_iff {A : FinHolAtlas d X} {L : LocPot X} {s : X → X → ℂ}
    (hs : IsSection A L s) {x y : X} (hy : y ∈ L.U x) : s x y = 0 ↔ s y y = 0 := by sorry
