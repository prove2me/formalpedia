-- Prove2me | Theorems.Thm_GlobalTheory_LogResInt_isAnalyticSubset_zero
-- name    : GlobalTheory.LogResInt.isAnalyticSubset_zero
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:14:07.460784+00:00
-- url     : https://prove2.me/theorems/d24ffc71-8517-4867-9d62-f7624437252b
-- title:
--   Log Res Int: is Analytic Subset zero
-- statement:
--   The Log Res Int construction uses the is Analytic Subset zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsClosedOfIsAnalyticSubset.lean#L80-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsClosedOfIsAnalyticSubset.lean#L80-L90

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

theorem GlobalTheory.LogResInt.isAnalyticSubset_zero {A : FinHolAtlas d X} {L : LocPot X} {s : X → X → ℂ}
    (hs : IsSection A L s) : A.IsAnalyticSubset {y | s y y = 0} := by sorry
