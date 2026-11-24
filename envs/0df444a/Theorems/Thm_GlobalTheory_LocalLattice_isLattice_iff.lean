-- Prove2me | Theorems.Thm_GlobalTheory_LocalLattice_isLattice_iff
-- name    : GlobalTheory.LocalLattice.isLattice_iff
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T18:13:38.419803+00:00
-- url     : https://prove2.me/theorems/cfe82079-73e2-4c51-8ba2-0e3ece113031
-- title:
--   Local Lattice: is Lattice iff
-- statement:
--   The Local Lattice construction uses the is Lattice iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/MemIffForallMemLocalizeRingOfIntegers.lean#L588-L590
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/MemIffForallMemLocalizeRingOfIntegers.lean#L588-L590

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

theorem GlobalTheory.LocalLattice.isLattice_iff {K : Type} [Field K] [NumberField K] {r : ℕ}
    (L : Submodule (𝓞 K) (Fin r → K)) : ReciprocityTheory.MultiplicativeHeights.IsLattice L ↔ Submodule.IsLattice K L := by sorry
