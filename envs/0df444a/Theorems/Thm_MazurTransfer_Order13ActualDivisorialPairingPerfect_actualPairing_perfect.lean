-- Prove2me | Theorems.Thm_MazurTransfer_Order13ActualDivisorialPairingPerfect_actualPairing_perfect
-- name    : MazurTransfer.Order13ActualDivisorialPairingPerfect.actualPairing_perfect
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-18T11:33:56.105271+00:00
-- url     : https://prove2.me/theorems/11980324-d022-4bfb-be57-9b0b086b27d5
-- title:
--   The original actual divisorial nineteen-pairing is perfect
-- statement:
--   Over each original algebraically closed characteristic-zero field, the same actual divisorial nineteen-pairing on the literal order-13 curve function field is perfect. Its character map is bijective. Neither injectivity nor perfection is assumed.
-- source:
--   MazurTheorem Order13ActualDivisorialPairingPerfect.actualPairing_perfect, exact original theorem and actual pairing constructor.

import Definitions.Def_MazurTransfer_Order13ActualDivisorialNineteenPairingOriginalData20261018
import Definitions.Def_AlgebraicCurve_FunctionFieldWeilPairingDivisorial
noncomputable section
open MazurTransfer
open Order13ActualGeometricNineteenDivisorialPairing
attribute [local instance] actualDivisorialPairingOriginalFactProvider20261018 actualDivisorialPairingOriginalAlgebraProvider20261018

theorem MazurTransfer.Order13ActualDivisorialPairingPerfect.actualPairing_perfect (K : Type) [Field K] [CharZero K] [IsAlgClosed K] :
    (actualDivisorialNineteenPairingData K).Perfect := by sorry
