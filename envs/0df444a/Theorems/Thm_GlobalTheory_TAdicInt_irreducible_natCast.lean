-- Prove2me | Theorems.Thm_GlobalTheory_TAdicInt_irreducible_natCast
-- name    : GlobalTheory.TAdicInt.irreducible_natCast
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T11:28:51.138881+00:00
-- url     : https://prove2.me/theorems/68d767bc-ab2a-46de-9a6e-98707d6c0f69
-- title:
--   TAdic Int: irreducible nat Cast
-- statement:
--   The TAdic Int construction uses the irreducible nat Cast property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/PadicResidueFieldCardAndPrimeIrreducible.lean#L26-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/PadicResidueFieldCardAndPrimeIrreducible.lean#L26-L29

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_PadicResidueFieldCardAndPrimeIrreducible
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel IsLocalRing
noncomputable section
open GlobalTheory GlobalTheory.TAdicInt

theorem GlobalTheory.TAdicInt.irreducible_natCast (T : ℕ) [Fact T.Prime] : Irreducible (T : 𝒪[ℚ_[T]]) := by sorry
