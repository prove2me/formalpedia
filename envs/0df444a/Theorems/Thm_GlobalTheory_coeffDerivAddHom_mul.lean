-- Prove2me | Theorems.Thm_GlobalTheory_coeffDerivAddHom_mul
-- name    : GlobalTheory.coeffDerivAddHom_mul
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T22:08:53.105802+00:00
-- url     : https://prove2.me/theorems/88ab14bc-fc31-4574-a13e-c174c607fb82
-- title:
--   Global Theory: coeff Deriv Add Hom mul
-- statement:
--   The Global Theory construction uses the coeff Deriv Add Hom mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DerivationExtendMvPolynomial.lean#L39-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DerivationExtendMvPolynomial.lean#L39-L51

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DerivationExtendMvPolynomial
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing TensorProduct
open GlobalTheory

theorem GlobalTheory.coeffDerivAddHom_mul {B τ : Type} [CommRing B] (D : Derivation ℤ B B)
    (p q : MvPolynomial τ B) :
    coeffDerivAddHom D (p * q) = p * coeffDerivAddHom D q + q * coeffDerivAddHom D p := by sorry
