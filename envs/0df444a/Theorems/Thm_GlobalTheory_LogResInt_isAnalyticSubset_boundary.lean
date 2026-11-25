-- Prove2me | Theorems.Thm_GlobalTheory_LogResInt_isAnalyticSubset_boundary
-- name    : GlobalTheory.LogResInt.isAnalyticSubset_boundary
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:14:25.604645+00:00
-- url     : https://prove2.me/theorems/d6290efd-5276-4940-a0c9-e87b69cd7ab4
-- title:
--   Log Res Int: is Analytic Subset boundary
-- statement:
--   The Log Res Int construction uses the is Analytic Subset boundary property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsClosedOfIsAnalyticSubset.lean#L92-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsClosedOfIsAnalyticSubset.lean#L92-L110

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

theorem GlobalTheory.LogResInt.isAnalyticSubset_boundary {A : FinHolAtlas d X} {m : ℕ} {Λ : Fin m → LocPot X}
    {σ : Fin m → X → X → ℂ} (hσ : ∀ i, IsSection A (Λ i) (σ i)) :
    A.IsAnalyticSubset (boundary σ) := by sorry
