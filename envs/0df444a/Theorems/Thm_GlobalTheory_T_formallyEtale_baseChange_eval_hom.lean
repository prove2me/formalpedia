-- Prove2me | Theorems.Thm_GlobalTheory_T_formallyEtale_baseChange_eval_hom
-- name    : GlobalTheory.T.formallyEtale_baseChange_eval_hom
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:32:14.056776+00:00
-- url     : https://prove2.me/theorems/f747c3d1-9432-425c-b7ff-df19074e8d1b
-- title:
--   T: formally Etale base Change eval hom
-- statement:
--   The T construction uses the formally Etale base Change eval hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FormallyEtaleBaseChangeEvalHomStatement.lean#L6-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FormallyEtaleBaseChangeEvalHomStatement.lean#L6-L10

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FormallyEtaleBaseChangeEvalHom
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FormallyEtaleBaseChangeEvalHomStatement
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

theorem GlobalTheory.T.formallyEtale_baseChange_eval_hom : ∀ {k R B : Type} [CommRing k] [CommRing R] [CommRing B] [Algebra k R] [Algebra k B] {r : ℕ} (τ : Fin r → B),
  (MvPolynomial.eval₂Hom (algebraMap k B) τ).FormallyEtale →
  (MvPolynomial.eval₂Hom (Algebra.TensorProduct.includeLeftRingHom : R →+* R ⊗[k] B)
      (fun i => (1 : R) ⊗ₜ[k] τ i)).FormallyEtale := by sorry
