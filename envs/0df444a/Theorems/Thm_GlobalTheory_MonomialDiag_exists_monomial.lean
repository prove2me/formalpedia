-- Prove2me | Theorems.Thm_GlobalTheory_MonomialDiag_exists_monomial
-- name    : GlobalTheory.MonomialDiag.exists_monomial
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:21:29.160153+00:00
-- url     : https://prove2.me/theorems/14a3b025-f2c9-4472-861c-6e0d2ba81429
-- title:
--   Monomial Diag: exists monomial
-- statement:
--   The Monomial Diag construction uses the exists monomial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/ExistsSignatureDecompositionDiagonal.lean#L97-L160
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/ExistsSignatureDecompositionDiagonal.lean#L97-L160

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SignatureConjugationInvariant
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_ExistsSignatureDecompositionDiagonal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory GlobalTheory.MonomialDiag

theorem GlobalTheory.MonomialDiag.exists_monomial : ∀ (n p q : ℕ) (G Q : Matrix (Fin n) (Fin n) ℂ) (d : Fin n → ℝ), Formalism.UG.HasSignature G p q → Q.det ≠ 0 → (∀ i, d i ≠ 0) → Qᴴ * G * Q = Matrix.diagonal (fun i => (d i : ℂ)) → ∃ A : Matrix (Fin p ⊕ Fin q) (Fin n) ℂ, Aᴴ * Formalism.UG.Jpq p q * A = G ∧ ∀ a i j, (A * Q) a i ≠ 0 → (A * Q) a j ≠ 0 → i = j := by sorry
