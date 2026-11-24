-- Prove2me | Theorems.Thm_GlobalTheory_MajPosCpx_gram_sub_eq
-- name    : GlobalTheory.MajPosCpx.gram_sub_eq
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T18:20:34.248865+00:00
-- url     : https://prove2.me/theorems/c1a68c29-5736-4137-ab47-ab4e1117dc13
-- title:
--   Maj Pos Cpx: gram sub eq
-- statement:
--   The Maj Pos Cpx construction uses the gram sub eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ComplexWittBasisNormalForm.lean#L12-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ComplexWittBasisNormalForm.lean#L12-L16

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

theorem GlobalTheory.MajPosCpx.gram_sub_eq {n r a b : ℕ} (J : Matrix (Fin n) (Fin n) ℂ) (X Y : Matrix (Fin n) (Fin r) ℂ)
    (f : Fin a → Fin r) (g : Fin b → Fin r) (R : Matrix (Fin a) (Fin b) ℂ)
    (hR : ∀ i j, (X.conjTranspose * J * Y) (f i) (g j) = R i j) :
    (X.submatrix id f).conjTranspose * J * (Y.submatrix id g) = R := by sorry
