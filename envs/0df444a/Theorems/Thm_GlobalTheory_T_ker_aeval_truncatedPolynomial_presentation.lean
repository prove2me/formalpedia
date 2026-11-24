-- Prove2me | Theorems.Thm_GlobalTheory_T_ker_aeval_truncatedPolynomial_presentation
-- name    : GlobalTheory.T.ker_aeval_truncatedPolynomial_presentation
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T20:51:34.730119+00:00
-- url     : https://prove2.me/theorems/6444e91e-f660-45a2-b413-04d82b00bacd
-- title:
--   T: ker aeval truncated Polynomial presentation
-- statement:
--   The T construction uses the ker aeval truncated Polynomial presentation property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/KerAevalTruncatedPolynomialPresentationStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/KerAevalTruncatedPolynomialPresentationStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KerAevalTruncatedPolynomialPresentation
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KerAevalTruncatedPolynomialPresentationStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.ker_aeval_truncatedPolynomial_presentation : ∀ (n : ℕ), 0 < n → ∀ (B A : Type) [CommRing B] [CommRing A] [Algebra B A] (d : ℕ) (x : Fin d → A) (b : Fin d → B), (∀ i, x i ^ n = algebraMap B A (b i)) → LinearIndependent B (fun a : Fin d → Fin n => ∏ i, x i ^ (a i : ℕ)) → RingHom.ker (MvPolynomial.aeval x : MvPolynomial (Fin d) B →ₐ[B] A) = Ideal.span (Set.range fun i : Fin d => (MvPolynomial.X i ^ n - MvPolynomial.C (b i) : MvPolynomial (Fin d) B)) := by sorry
