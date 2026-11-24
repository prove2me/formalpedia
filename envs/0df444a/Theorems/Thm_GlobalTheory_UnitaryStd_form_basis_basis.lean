-- Prove2me | Theorems.Thm_GlobalTheory_UnitaryStd_form_basis_basis
-- name    : GlobalTheory.UnitaryStd.form_basis_basis
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T21:45:56.865327+00:00
-- url     : https://prove2.me/theorems/2f9b02fd-8b62-4f73-adf6-c203b4c7c65d
-- title:
--   Unitary Std: form basis basis
-- statement:
--   The Unitary Std construction uses the form basis basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UnitaryStandardLatticeAlternatingFormBijective.lean#L7-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UnitaryStandardLatticeAlternatingFormBijective.lean#L7-L16

import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_BasisApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryStandardLatticeAlternatingFormBijective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open scoped TensorProduct
open GlobalTheory GlobalTheory.UnitaryStd

theorem GlobalTheory.UnitaryStd.form_basis_basis {E : Type} [Field E] [NumberField E] {r : ℕ} (ρ : 𝓞 E →+* Matrix (Fin r) (Fin r) ℤ)
    (g : ℕ) (S : Matrix (Fin r) (Fin r) ℤ) (i j : Fin r) (a c : Fin g ⊕ Fin g) :
    form ρ g S (basis ρ g (j, c)) (basis ρ g (i, a)) =
      S j i * (Matrix.J (Fin g) ℤ) a c := by sorry
