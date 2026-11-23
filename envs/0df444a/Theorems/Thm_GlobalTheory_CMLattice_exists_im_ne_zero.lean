-- Prove2me | Theorems.Thm_GlobalTheory_CMLattice_exists_im_ne_zero
-- name    : GlobalTheory.CMLattice.exists_im_ne_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:39:02.686813+00:00
-- url     : https://prove2.me/theorems/32825b09-fafa-4ce7-a3de-e115302cf87c
-- title:
--   CMLattice: exists im ne zero
-- statement:
--   The CMLattice construction uses the exists im ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/LatticeCmEqIdealAndCovolume.lean#L13-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/LatticeCmEqIdealAndCovolume.lean#L13-L23

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_LatticeCmEqIdealAndCovolume
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex NumberField Module
open scoped nonZeroDivisors
open GlobalTheory
open GlobalTheory.CMLattice
variable {K : Type} [Field K] [NumberField K]

theorem GlobalTheory.CMLattice.exists_im_ne_zero (σ : K →+* ℂ) (hσ : ¬ ComplexEmbedding.IsReal σ) :
    ∃ a : 𝓞 K, (σ (a : K)).im ≠ 0 := by sorry
