-- Prove2me | Theorems.Thm_GlobalTheory_T_unitaryStandardLatticeAlternatingForm_bijective
-- name    : GlobalTheory.T.unitaryStandardLatticeAlternatingForm_bijective
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:40:12.208264+00:00
-- url     : https://prove2.me/theorems/c503d61f-877d-5724-a87b-9d4743892c35
-- title:
--   T: unitary Standard Lattice Alternating Form bijective
-- statement:
--   The T construction uses the unitary Standard Lattice Alternating Form bijective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UnitaryStandardLatticeAlternatingFormBijectiveStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UnitaryStandardLatticeAlternatingFormBijectiveStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryStandardLatticeAlternatingFormBijective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_BasisApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryStandardLatticeAlternatingFormBijectiveStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open scoped TensorProduct
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.unitaryStandardLatticeAlternatingForm_bijective : ∀ {E : Type} [Field E] [NumberField E] {r : ℕ} (ρ : 𝓞 E →+* Matrix (Fin r) (Fin r) ℤ) (g : ℕ) (S : Matrix (Fin r) (Fin r) ℤ), IsUnit S.det → Function.Bijective (GlobalTheory.UnitaryStd.form ρ g S) := by sorry
