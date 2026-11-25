-- Prove2me | Theorems.Thm_GlobalTheory_SignChar_pairing_zero_right
-- name    : GlobalTheory.SignChar.pairing_zero_right
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:36:41.639444+00:00
-- url     : https://prove2.me/theorems/4cbc530b-01d5-49e7-b919-8b60d609f3cb
-- title:
--   Sign Char: pairing zero right
-- statement:
--   The Sign Char construction uses the pairing zero right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/PairingNsmulRight.lean#L27-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/PairingNsmulRight.lean#L27-L29

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

theorem GlobalTheory.SignChar.pairing_zero_right (N : ℕ) (x : B.G R) (hx : N • x = 0) : B.IsPairing N x 0 1 := by sorry
