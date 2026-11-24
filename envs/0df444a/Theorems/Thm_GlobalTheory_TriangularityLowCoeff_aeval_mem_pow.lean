-- Prove2me | Theorems.Thm_GlobalTheory_TriangularityLowCoeff_aeval_mem_pow
-- name    : GlobalTheory.TriangularityLowCoeff.aeval_mem_pow
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T21:12:13.434202+00:00
-- url     : https://prove2.me/theorems/ea3941d4-7cd4-47ad-a850-583656c7fa3f
-- title:
--   Triangularity Low Coeff: aeval mem pow
-- statement:
--   The Triangularity Low Coeff construction uses the aeval mem pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CoeffAnnihilatedOfAevalMemKerPow.lean#L100-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CoeffAnnihilatedOfAevalMemKerPow.lean#L100-L109

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

theorem GlobalTheory.TriangularityLowCoeff.aeval_mem_pow {R B : Type} [CommRing R] [CommRing B] [Algebra R B] {d : ℕ}
    (ε : B →ₐ[R] R) (y : Fin d → B) (hy : ∀ i, ε (y i) = 0) (n : ℕ) (Q : MvPolynomial (Fin d) R)
    (hQ : Q ∈ idealOfVars (Fin d) R ^ n) : aeval y Q ∈ RingHom.ker ε ^ n := by sorry
