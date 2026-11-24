-- Prove2me | Theorems.Thm_GlobalTheory_CMLattice_mem_iff
-- name    : GlobalTheory.CMLattice.mem_iff
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T11:02:43.163844+00:00
-- url     : https://prove2.me/theorems/bd4b08f1-8728-4316-be63-e09a98b95b50
-- title:
--   CMLattice: mem iff
-- statement:
--   The CMLattice construction uses the mem iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/LatticeCmEqIdealAndCovolume.lean#L167-L202
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/LatticeCmEqIdealAndCovolume.lean#L167-L202

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

theorem GlobalTheory.CMLattice.mem_iff (σ : K →+* ℂ) (L L' : PeriodPair) (𝔟 : Ideal (𝓞 K)) (β : ℂ) (h𝔟 : 𝔟 ≠ ⊥)
    (hβ : β ≠ 0)
    (h1 : ∀ x : K, (∀ b ∈ 𝔟, IsIntegral ℤ (x * (b : K))) → ∀ z ∈ L.lattice,
      β * σ x * z ∈ L'.lattice)
    (h2 : ∀ y ∈ 𝔟, ∀ z ∈ L'.lattice, β⁻¹ * σ (y : K) * z ∈ L.lattice) (z : ℂ) :
    z ∈ L'.lattice ↔ ∀ y ∈ 𝔟, β⁻¹ * σ (y : K) * z ∈ L.lattice := by sorry
