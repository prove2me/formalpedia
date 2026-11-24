-- Prove2me | Theorems.Thm_GlobalTheory_exists_linear_increment
-- name    : GlobalTheory.exists_linear_increment
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T22:34:11.815889+00:00
-- url     : https://prove2.me/theorems/e47b04a7-562f-47ec-8b5d-04dfdd420360
-- title:
--   Global Theory: exists linear increment
-- statement:
--   The Global Theory construction uses the exists linear increment property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/LevelThreeSeparatesTangents.lean#L22-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/LevelThreeSeparatesTangents.lean#L22-L93

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_LevelThreeSeparatesTangents
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex ReciprocityTheory.ChartRestriction.G.I2 Filter Topology
open GlobalTheory
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem GlobalTheory.exists_linear_increment {U : Set V} (ho : IsOpen U) (hd : Dense U) {f : V → ℂ} {c₀ : ℂ}
    (hf : ∀ a ∈ U, ∀ b ∈ U, -a - b ∈ U → c₀ + f a + f b + f (-a - b) = 0)
    {a₀ : V} (ha₀ : a₀ ∈ U) (hdf : DifferentiableAt ℂ f a₀) :
    ∃ L : V →L[ℂ] ℂ, ∀ a t, a ∈ U → a + t ∈ U → f (a + t) - f a = L t := by sorry
