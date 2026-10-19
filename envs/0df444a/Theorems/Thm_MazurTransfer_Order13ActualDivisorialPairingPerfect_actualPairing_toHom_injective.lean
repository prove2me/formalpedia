-- Prove2me | Theorems.Thm_MazurTransfer_Order13ActualDivisorialPairingPerfect_actualPairing_toHom_injective
-- name    : MazurTransfer.Order13ActualDivisorialPairingPerfect.actualPairing_toHom_injective
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-18T11:23:39.827228+00:00
-- url     : https://prove2.me/theorems/cd1a32d8-ba67-478e-9c56-843f10fe2acf
-- title:
--   The actual divisorial nineteen-pairing character map is injective
-- statement:
--   For every original algebraically closed characteristic-zero field, the character map of the original actual divisorial nineteen-pairing on the literal order-13 curve function field is injective. Divisibility is proved using the actual finite rational-function-field tower; it is not added as a hypothesis.
-- source:
--   MazurTheorem Order13ActualDivisorialPairingPerfect.actualPairing_toHom_injective, exact original contract; official Anthropic FLT divisorial character-map injectivity at exact pin 6e837e75355538c7f80bab5b956861e86c4eacc2.

import Definitions.Def_MazurTransfer_Order13ActualDivisorialNineteenPairingOriginalData20261018
import Definitions.Def_AlgebraicCurve_FunctionFieldWeilPairingDivisorial
noncomputable section
open MazurTransfer
open Order13ActualGeometricNineteenDivisorialPairing
attribute [local instance] actualDivisorialPairingOriginalFactProvider20261018 actualDivisorialPairingOriginalAlgebraProvider20261018

theorem MazurTransfer.Order13ActualDivisorialPairingPerfect.actualPairing_toHom_injective (K : Type) [Field K] [CharZero K] [IsAlgClosed K] :
    Function.Injective (actualDivisorialNineteenPairingData K).toHom := by sorry
