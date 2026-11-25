-- Prove2me | Theorems.Thm_GlobalTheory_T_etale_polynomial_substitution
-- name    : GlobalTheory.T.etale_polynomial_substitution
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:28:38.97929+00:00
-- url     : https://prove2.me/theorems/7bb1bbcb-fc8f-42d8-8255-8425fed31b68
-- title:
--   T: etale polynomial substitution
-- statement:
--   The T construction uses the etale polynomial substitution property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/EtalePolynomialSubstitutionStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/EtalePolynomialSubstitutionStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EtalePolynomialSubstitution
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EtalePolynomialSubstitutionStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem GlobalTheory.T.etale_polynomial_substitution : ∀ {k A R N : Type} [CommRing k] [CommRing A] [CommRing R] (α : k →+* A) (t : A) (f : A →+* R) (n : N → R) {d : ℕ} (e : Fin (d + 1) ≃ Option N), (MvPolynomial.eval₂Hom α (fun _ : Fin 1 => t)).Etale → Function.Bijective (MvPolynomial.eval₂Hom f n) → (MvPolynomial.eval₂Hom (f.comp α) (fun j => (e j).elim (f t) n)).Etale := by sorry
