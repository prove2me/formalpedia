-- Prove2me | Theorems.Thm_GlobalTheory_LogResInt_isAnalyticSubset_inter
-- name    : GlobalTheory.LogResInt.isAnalyticSubset_inter
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T18:19:06.131862+00:00
-- url     : https://prove2.me/theorems/a7ffb101-e794-401f-9a38-6d351be144f7
-- title:
--   Log Res Int: is Analytic Subset inter
-- statement:
--   The Log Res Int construction uses the is Analytic Subset inter property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsClosedOfIsAnalyticSubset.lean#L45-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsClosedOfIsAnalyticSubset.lean#L45-L67

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

theorem GlobalTheory.LogResInt.isAnalyticSubset_inter {A : FinHolAtlas d X} {S T : Set X} (hS : A.IsAnalyticSubset S)
    (hT : A.IsAnalyticSubset T) : A.IsAnalyticSubset (S ∩ T) := by sorry
