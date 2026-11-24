-- Prove2me | Theorems.Thm_GlobalTheory_Klein_exists_hasDerivAt_intFun
-- name    : GlobalTheory.Klein.exists_hasDerivAt_intFun
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T21:46:01.416324+00:00
-- url     : https://prove2.me/theorems/a5dec0fa-bded-4f92-a002-d24c74905661
-- title:
--   Klein: exists has Deriv At int Fun
-- statement:
--   The Klein construction uses the exists has Deriv At int Fun property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/NormIteratedDerivWeierstrassPLeOne.lean#L79-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/NormIteratedDerivWeierstrassPLeOne.lean#L79-L109

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

theorem GlobalTheory.Klein.exists_hasDerivAt_intFun {ι : ℂ ≃+* ℂ_[p]} {L : PeriodPair} {r : ℂ} (hg : Good ι L r)
    {f : ℂ → ℂ} (hf : f ∈ intFun ι L r) :
    ∃ g ∈ intFun ι L r, ∀ w ∉ L.lattice, HasDerivAt f (g w) w := by sorry
