-- Prove2me | Theorems.Thm_GlobalTheory_SignChar_pairing_nsmul_right
-- name    : GlobalTheory.SignChar.pairing_nsmul_right
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T20:13:18.838857+00:00
-- url     : https://prove2.me/theorems/b06daee5-d5d5-4ef2-93f2-654cf1a12d7a
-- title:
--   Sign Char: pairing nsmul right
-- statement:
--   The Sign Char construction uses the pairing nsmul right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/PairingNsmulRight.lean#L41-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/PairingNsmulRight.lean#L41-L49

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_EvenTwoEvaluationSign
import Definitions.Def_ReciprocityTheory_DualLattices_IsPairingValueAddRight
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_PairingNsmulRight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct IsLocalRing Matrix ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2
noncomputable section
open GlobalTheory
open GlobalTheory.SignChar
variable {R₀ : Type} [CommRing R₀]
variable (B : BX R₀) {R : LAlg R₀}

theorem GlobalTheory.SignChar.pairing_nsmul_right (N : ℕ) (x y : B.G R) (z : (R : Type)ˣ) (h : B.IsPairing N x y z)
    (n : ℕ) : B.IsPairing N x (n • y) (z ^ n) := by sorry
