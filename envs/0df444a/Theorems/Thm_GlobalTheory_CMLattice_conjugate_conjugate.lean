-- Prove2me | Theorems.Thm_GlobalTheory_CMLattice_conjugate_conjugate
-- name    : GlobalTheory.CMLattice.conjugate_conjugate
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:27:38.119601+00:00
-- url     : https://prove2.me/theorems/258c2b08-7d7d-4b1c-ac8a-48d609a0388b
-- title:
--   CMLattice: conjugate conjugate
-- statement:
--   The CMLattice construction uses the conjugate conjugate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusSplitting/EqTopOfForallEmbAllMem.lean#L13-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusSplitting/EqTopOfForallEmbAllMem.lean#L13-L15

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TorusAtData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusSplitting_EqTopOfForallEmbAllMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.I2
open GlobalTheory GlobalTheory.CMLattice
noncomputable section
variable {E : Type} [Field E] [NumberField E]
omit [NumberField E]

theorem GlobalTheory.CMLattice.conjugate_conjugate (τ : E →+* ℂ) :
    ComplexEmbedding.conjugate (ComplexEmbedding.conjugate τ) = τ := by sorry
