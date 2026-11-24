-- Prove2me | Theorems.Thm_GlobalTheory_LogResInt_holoOn_continuousAt
-- name    : GlobalTheory.LogResInt.holoOn_continuousAt
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T18:19:12.555287+00:00
-- url     : https://prove2.me/theorems/daac1cd1-a277-4676-af91-ef952e49ba6d
-- title:
--   Log Res Int: holo On continuous At
-- statement:
--   The Log Res Int construction uses the holo On continuous At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsClosedOfIsAnalyticSubset.lean#L22-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsClosedOfIsAnalyticSubset.lean#L22-L32

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

theorem GlobalTheory.LogResInt.holoOn_continuousAt {A : FinHolAtlas d X} {W : Set X} {f : X → ℂ} (hf : A.HoloOn W f)
    {x : X} (hx : x ∈ W) : ContinuousAt f x := by sorry
