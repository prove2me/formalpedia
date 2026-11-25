-- Prove2me | Theorems.Thm_GlobalTheory_SignChar_pairing_sum_right
-- name    : GlobalTheory.SignChar.pairing_sum_right
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T20:14:13.49588+00:00
-- url     : https://prove2.me/theorems/26c85272-25e3-4e53-a904-c2ea334d7192
-- title:
--   Sign Char: pairing sum right
-- statement:
--   The Sign Char construction uses the pairing sum right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/PairingNsmulRight.lean#L63-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/PairingNsmulRight.lean#L63-L73

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

theorem GlobalTheory.SignChar.pairing_sum_right {ι : Type} (s : Finset ι) (N : ℕ) (x : B.G R) (y : ι → B.G R)
    (z : ι → (R : Type)ˣ) (hx : N • x = 0) (h : ∀ i, B.IsPairing N x (y i) (z i)) :
    B.IsPairing N x (∑ i ∈ s, y i) (∏ i ∈ s, z i) := by sorry
