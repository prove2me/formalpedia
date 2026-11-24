-- Prove2me | Theorems.Thm_GlobalTheory_SplitFlip_Model_isPrimFrame_mul
-- name    : GlobalTheory.SplitFlip.Model.isPrimFrame_mul
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T20:20:00.273847+00:00
-- url     : https://prove2.me/theorems/48d94033-f3f0-4585-ae8f-d8e1041c9ee9
-- title:
--   Model: is Prim Frame mul
-- statement:
--   The Model construction uses the is Prim Frame mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/OmAUnipFourierInv.lean#L18-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/OmAUnipFourierInv.lean#L18-L40

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_OmAUnipFourierInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped NNReal ENNReal Pointwise
noncomputable section
open GlobalTheory GlobalTheory.SplitFlip GlobalTheory.SplitFlip.Model
open GlobalTheory.SplitWeil GlobalTheory.SplitWeil.Model GlobalTheory.SplitFlip
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {A A' D : Type*} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A'] [Fintype D] [DecidableEq D]
omit [DecidableEq A]

theorem GlobalTheory.SplitFlip.Model.isPrimFrame_mul {Λ Λ' : Submodule 𝒪[k] (D → k)} {X : Matrix A D k} (hX : IsPrimFrame Λ X) (g : GL D k)
    (hg : ∀ x, x ᵥ* g.val ∈ Λ' ↔ x ∈ Λ) : IsPrimFrame Λ' (X * g.val) := by sorry
