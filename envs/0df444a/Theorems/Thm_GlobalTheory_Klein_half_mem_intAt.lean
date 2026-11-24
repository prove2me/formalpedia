-- Prove2me | Theorems.Thm_GlobalTheory_Klein_half_mem_intAt
-- name    : GlobalTheory.Klein.half_mem_intAt
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T21:45:50.322691+00:00
-- url     : https://prove2.me/theorems/2ae4c104-5cc6-442b-975a-de324980a5dc
-- title:
--   Klein: half mem int At
-- statement:
--   The Klein construction uses the half mem int At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/NormIteratedDerivWeierstrassPLeOne.lean#L28-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/NormIteratedDerivWeierstrassPLeOne.lean#L28-L35

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_NotRedOfMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_WeierstrassPAddOfNeOfDerivNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_NormIteratedDerivWeierstrassPLeOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.L2.Th1.F GlobalTheory.Klein
open scoped ComplexConjugate BigOperators
noncomputable section
open GlobalTheory GlobalTheory.Klein
variable {p : ℕ} [Fact p.Prime]

theorem GlobalTheory.Klein.half_mem_intAt (ι : ℂ ≃+* ℂ_[p]) (hp : p ≠ 2) : (2⁻¹ : ℂ) ∈ intAt ι := by sorry
