-- Prove2me | Theorems.Thm_GlobalTheory_LocalLattice_hermPairing_apply
-- name    : GlobalTheory.LocalLattice.hermPairing_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:37:01.553797+00:00
-- url     : https://prove2.me/theorems/93374a0d-93c8-411f-9059-51e66dd731e7
-- title:
--   Local Lattice: herm Pairing apply
-- statement:
--   The Local Lattice construction uses the herm Pairing apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/MemIffForallMemLocalizeRingOfIntegers.lean#L620-L621
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/MemIffForallMemLocalizeRingOfIntegers.lean#L620-L621

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
open ReciprocityTheory.ChartRestriction.G.FD
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem GlobalTheory.LocalLattice.hermPairing_apply (G : Matrix (Fin r) (Fin r) E) (x y : Fin r → E) :
    hermPairing G x y = herm G x y := by sorry

attribute [defeq] GlobalTheory.LocalLattice.hermPairing_apply
