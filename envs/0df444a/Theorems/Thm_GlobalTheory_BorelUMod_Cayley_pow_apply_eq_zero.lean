-- Prove2me | Theorems.Thm_GlobalTheory_BorelUMod_Cayley_pow_apply_eq_zero
-- name    : GlobalTheory.BorelUMod.Cayley.pow_apply_eq_zero
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T11:01:18.722642+00:00
-- url     : https://prove2.me/theorems/9197570f-b41c-4b89-b196-1f6f263eb21f
-- title:
--   Cayley: pow apply eq zero
-- statement:
--   The Cayley construction uses the pow apply eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RelIndexEqOfSurj.lean#L31-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RelIndexEqOfSurj.lean#L31-L39

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LineOppositeParabolicUnitaryLeviSectionEq
import Definitions.Def_Formalism_SatakeDualWeyl_StatementE
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemGUIffAdjJ
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PowApplyEqZeroOfStrictUpper
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RelIndexEqOfSurj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.LGrp GlobalTheory.BorelUMod Formalism.UG
noncomputable section
open GlobalTheory GlobalTheory.BorelUMod GlobalTheory.BorelUMod.Cayley
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ}
omit [Valued L (WithZero (Multiplicative ℤ))]

theorem GlobalTheory.BorelUMod.Cayley.pow_apply_eq_zero {y : Matrix (Fin n) (Fin n) L} (hy : ∀ i j, j ≤ i → y i j = 0) (k : ℕ) :
    ∀ i j : Fin n, j.val < i.val + k → (y ^ k) i j = 0 := by sorry
