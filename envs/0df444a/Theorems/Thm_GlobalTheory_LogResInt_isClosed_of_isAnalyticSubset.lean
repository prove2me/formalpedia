-- Prove2me | Theorems.Thm_GlobalTheory_LogResInt_isClosed_of_isAnalyticSubset
-- name    : GlobalTheory.LogResInt.isClosed_of_isAnalyticSubset
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:14:05.830802+00:00
-- url     : https://prove2.me/theorems/e8850216-ce88-5e63-ab3c-e3974914cb42
-- title:
--   Log Res Int: is Closed of is Analytic Subset
-- statement:
--   The Log Res Int construction uses the is Closed of is Analytic Subset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsClosedOfIsAnalyticSubset.lean#L34-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsClosedOfIsAnalyticSubset.lean#L34-L43

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

theorem GlobalTheory.LogResInt.isClosed_of_isAnalyticSubset {A : FinHolAtlas d X} {S : Set X}
    (hS : A.IsAnalyticSubset S) : IsClosed S := by sorry
