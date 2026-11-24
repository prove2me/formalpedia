-- Prove2me | Theorems.Thm_GlobalTheory_MajPosCpx_mul_submatrix_id
-- name    : GlobalTheory.MajPosCpx.mul_submatrix_id
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T18:20:28.208391+00:00
-- url     : https://prove2.me/theorems/a75ebee3-2baa-4275-8fc8-1c015112da72
-- title:
--   Maj Pos Cpx: mul submatrix id
-- statement:
--   The Maj Pos Cpx construction uses the mul submatrix id property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ComplexWittBasisNormalForm.lean#L18-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ComplexWittBasisNormalForm.lean#L18-L20

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ConjTransposeMulMulSelfOfUnitaryConjStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PosDefExistsConjTransposeMulMulEqOneStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RadicalEltMovingDualToMajorantStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsLeviElementIsotropicOrthogonalComplexStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HermitianFlagComplementPosDefFactorizationStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HermitianFlagUnipotentMatrixExistsSparseStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ComplexWittBasisNormalForm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ComplexOrder
open GlobalTheory GlobalTheory.MajPosCpx

theorem GlobalTheory.MajPosCpx.mul_submatrix_id {n r a : ℕ} (u : Matrix (Fin n) (Fin n) ℂ) (X : Matrix (Fin n) (Fin r) ℂ)
    (f : Fin a → Fin r) : u * X.submatrix id f = (u * X).submatrix id f := by sorry
