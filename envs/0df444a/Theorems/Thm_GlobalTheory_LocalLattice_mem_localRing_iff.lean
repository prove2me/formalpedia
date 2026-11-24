-- Prove2me | Theorems.Thm_GlobalTheory_LocalLattice_mem_localRing_iff
-- name    : GlobalTheory.LocalLattice.mem_localRing_iff
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T18:13:46.281269+00:00
-- url     : https://prove2.me/theorems/31bd7327-1f23-4a5f-be79-b7a57e0c81a6
-- title:
--   Local Lattice: mem local Ring iff
-- statement:
--   The Local Lattice construction uses the mem local Ring iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/MemIffForallMemLocalizeRingOfIntegers.lean#L124-L132
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/MemIffForallMemLocalizeRingOfIntegers.lean#L124-L132

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
variable {O : Type*} (K : Type*) [CommRing O] [IsDedekindDomain O] [Field K] [Algebra O K]
  [IsFractionRing O K]
  {V : Type*} [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V]
variable {K}

theorem GlobalTheory.LocalLattice.mem_localRing_iff (v : HeightOneSpectrum O) (x : K) :
    x ∈ v.valuationSubringAtPrime K ↔ ∃ s ∉ v.asIdeal, s • x ∈ (1 : Submodule O K) := by sorry
