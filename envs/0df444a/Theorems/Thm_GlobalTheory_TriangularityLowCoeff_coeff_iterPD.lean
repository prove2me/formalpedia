-- Prove2me | Theorems.Thm_GlobalTheory_TriangularityLowCoeff_coeff_iterPD
-- name    : GlobalTheory.TriangularityLowCoeff.coeff_iterPD
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T21:12:14.775224+00:00
-- url     : https://prove2.me/theorems/c2188667-d967-4ad3-8b00-22a80b1dd1db
-- title:
--   Triangularity Low Coeff: coeff iter PD
-- statement:
--   The Triangularity Low Coeff construction uses the coeff iter PD property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CoeffAnnihilatedOfAevalMemKerPow.lean#L90-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CoeffAnnihilatedOfAevalMemKerPow.lean#L90-L98

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CoeffAnnihilatedOfAevalMemKerPow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory GlobalTheory.TriangularityLowCoeff
open MvPolynomial

theorem GlobalTheory.TriangularityLowCoeff.coeff_iterPD {R : Type} [CommRing R] {d : ℕ} :
    ∀ (L : List (Fin d)) (m : Fin d →₀ ℕ) (Q : MvPolynomial (Fin d) R),
      coeff m (iterDer (fun i => pderiv i) L Q) = coeff (m + expOf L) Q * (fac L m : R)
  := by sorry
