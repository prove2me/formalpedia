-- Prove2me | Theorems.Thm_GlobalTheory_LocalLattice_mem_iff_forall_mem_localize_ringOfIntegers
-- name    : GlobalTheory.LocalLattice.mem_iff_forall_mem_localize_ringOfIntegers
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T18:13:45.902858+00:00
-- url     : https://prove2.me/theorems/f6e16d94-294d-472a-8cc2-da93e5cb76ac
-- title:
--   Local Lattice: mem iff forall mem localize ring Of Integers
-- statement:
--   The Local Lattice construction uses the mem iff forall mem localize ring Of Integers property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/MemIffForallMemLocalizeRingOfIntegers.lean#L597-L602
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/MemIffForallMemLocalizeRingOfIntegers.lean#L597-L602

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

theorem GlobalTheory.LocalLattice.mem_iff_forall_mem_localize_ringOfIntegers {K V : Type*} [Field K] [NumberField K]
    [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    (L : Submodule (𝓞 K) V) (x : V) :
    x ∈ L ↔ ∀ v : HeightOneSpectrum (𝓞 K), x ∈ localize K v L := by sorry
