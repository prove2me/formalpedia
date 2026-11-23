-- Prove2me | Theorems.Thm_GlobalTheory_DegreeGrowth_mem_boxSpan
-- name    : GlobalTheory.DegreeGrowth.mem_boxSpan
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:33:19.116149+00:00
-- url     : https://prove2.me/theorems/9c3cc343-3398-4a68-a0e3-da1fbc8f56f0
-- title:
--   Degree Growth: mem box Span
-- statement:
--   The Degree Growth construction uses the mem box Span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/FinrankTotalDegreeImageGrowth.lean#L18-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/FinrankTotalDegreeImageGrowth.lean#L18-L20

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FinrankTotalDegreeImageGrowth
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open GlobalTheory.DegreeGrowth
variable {K B : Type} [Field K] [CommRing B] [Algebra K B]

theorem GlobalTheory.DegreeGrowth.mem_boxSpan {s n : ℕ} (y : Fin s → B) (b : Fin n → B) (D : ℕ) (a : Fin s → ℕ)
    (ha : ∀ i, a i ≤ D) (l : Fin n) : (∏ i, y i ^ a i) * b l ∈ boxSpan K y b D := by sorry
