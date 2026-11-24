-- Prove2me | Theorems.Thm_GlobalTheory_UnitaryStd_toMatrix_basis_dualBasis_form
-- name    : GlobalTheory.UnitaryStd.toMatrix_basis_dualBasis_form
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T21:45:54.728745+00:00
-- url     : https://prove2.me/theorems/59e19722-0b05-42e5-8fee-766934df98b5
-- title:
--   Unitary Std: to Matrix basis dual Basis form
-- statement:
--   The Unitary Std construction uses the to Matrix basis dual Basis form property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UnitaryStandardLatticeAlternatingFormBijective.lean#L18-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UnitaryStandardLatticeAlternatingFormBijective.lean#L18-L24

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

theorem GlobalTheory.UnitaryStd.toMatrix_basis_dualBasis_form {E : Type} [Field E] [NumberField E] {r : ℕ} (ρ : 𝓞 E →+* Matrix (Fin r) (Fin r) ℤ)
    (g : ℕ) (S : Matrix (Fin r) (Fin r) ℤ) :
    LinearMap.toMatrix (basis ρ g) (basis ρ g).dualBasis (form ρ g S) =
      Matrix.kroneckerMap (· * ·) S.transpose (Matrix.J (Fin g) ℤ) := by sorry
