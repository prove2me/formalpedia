-- Prove2me | Theorems.Thm_GlobalTheory_LocalLattice_hermPairing_separating
-- name    : GlobalTheory.LocalLattice.hermPairing_separating
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T18:13:39.370214+00:00
-- url     : https://prove2.me/theorems/532b3b2d-8ae8-4281-83e1-b7d2e767db40
-- title:
--   Local Lattice: herm Pairing separating
-- statement:
--   The Local Lattice construction uses the herm Pairing separating property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/MemIffForallMemLocalizeRingOfIntegers.lean#L623-L627
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/MemIffForallMemLocalizeRingOfIntegers.lean#L623-L627

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

theorem GlobalTheory.LocalLattice.hermPairing_separating {G : Matrix (Fin r) (Fin r) E} (hG : G.det ≠ 0) (x : Fin r → E)
    (hx : ∀ y, hermPairing G x y = 0) : x = 0 := by sorry
