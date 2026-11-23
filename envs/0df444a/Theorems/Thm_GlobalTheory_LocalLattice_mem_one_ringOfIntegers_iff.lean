-- Prove2me | Theorems.Thm_GlobalTheory_LocalLattice_mem_one_ringOfIntegers_iff
-- name    : GlobalTheory.LocalLattice.mem_one_ringOfIntegers_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:39:54.653664+00:00
-- url     : https://prove2.me/theorems/50c70550-add8-45b5-93c4-095c7d5784ca
-- title:
--   Local Lattice: mem one ring Of Integers iff
-- statement:
--   The Local Lattice construction uses the mem one ring Of Integers iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/MemIffForallMemLocalizeRingOfIntegers.lean#L592-L595
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/MemIffForallMemLocalizeRingOfIntegers.lean#L592-L595

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_MemSaturatedOrderIsoSubspaceSpanSymmApply
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorsionNonvanishStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_MemIffForallMemLocalizeRingOfIntegers
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Matrix
open scoped nonZeroDivisors
noncomputable section
open GlobalTheory GlobalTheory.LocalLattice
set_option linter.unusedSectionVars false
open NumberField

theorem GlobalTheory.LocalLattice.mem_one_ringOfIntegers_iff {K : Type*} [Field K] [NumberField K] (x : K) :
    x ∈ (1 : Submodule (𝓞 K) K) ↔ IsIntegral ℤ x := by sorry
