-- Prove2me | Theorems.Thm_GlobalTheory_DegreeGrowth_monomial_mul_mem
-- name    : GlobalTheory.DegreeGrowth.monomial_mul_mem
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T03:41:04.459177+00:00
-- url     : https://prove2.me/theorems/84d7398c-e694-4310-8cb6-a82ae2c741e4
-- title:
--   Degree Growth: monomial mul mem
-- statement:
--   The Degree Growth construction uses the monomial mul mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/FinrankTotalDegreeImageGrowth.lean#L33-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/FinrankTotalDegreeImageGrowth.lean#L33-L46

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

theorem GlobalTheory.DegreeGrowth.monomial_mul_mem {s n : ℕ} (y : Fin s → B) (b : Fin n → B) (D d : ℕ) (a : Fin s → ℕ)
    (ha : ∀ i, a i ≤ d) {x : B} (hx : x ∈ boxSpan K y b D) :
    (∏ i, y i ^ a i) * x ∈ boxSpan K y b (D + d) := by sorry
