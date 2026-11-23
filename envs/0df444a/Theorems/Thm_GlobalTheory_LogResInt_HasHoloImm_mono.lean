-- Prove2me | Theorems.Thm_GlobalTheory_LogResInt_HasHoloImm_mono
-- name    : GlobalTheory.LogResInt.HasHoloImm.mono
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:57:24.924264+00:00
-- url     : https://prove2.me/theorems/d5087e1f-9bf5-4378-a5c2-e593e74aa748
-- title:
--   Has Holo Imm: mono
-- statement:
--   The Has Holo Imm construction uses the mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsClosedOfIsAnalyticSubset.lean#L17-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsClosedOfIsAnalyticSubset.lean#L17-L20

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

theorem GlobalTheory.LogResInt.HasHoloImm.mono {A : FinHolAtlas d X} {T T' : Set X} {k : ℕ} (h : HasHoloImm A T k)
    (hT : T ⊆ T') : HasHoloImm A T' k := by sorry
