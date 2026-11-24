-- Prove2me | Theorems.Thm_GlobalTheory_T_matrixImage_adjoint_mul_eq_of_selfDual_lattices
-- name    : GlobalTheory.T.matrixImage_adjoint_mul_eq_of_selfDual_lattices
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T20:52:55.090992+00:00
-- url     : https://prove2.me/theorems/fe492f47-e188-485c-aeb6-b722e0f28414
-- title:
--   T: matrix Image adjoint mul eq of self Dual lattices
-- statement:
--   The T construction uses the matrix Image adjoint mul eq of self Dual lattices property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MatrixImageAdjointMulEqOfSelfDualLatticesStatement.lean#L8-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MatrixImageAdjointMulEqOfSelfDualLatticesStatement.lean#L8-L12

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MatrixImageAdjointMulEqOfSelfDualLattices
import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemMatLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MatrixImageAdjointMulEqOfSelfDualLatticesStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Matrix GlobalTheory.LatOrb
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.matrixImage_adjoint_mul_eq_of_selfDual_lattices : ∀ {O K : Type} [CommRing O] [Field K] [Algebra O K] (σ : K →+* K),
    (∀ x, σ (σ x) = x) → ∀ (n : ℕ) (x : Matrix (Fin n) (Fin n) K), IsUnit x →
    ∀ M : Submodule O (Fin n → K), SelfDual O σ M → SelfDual O σ (matLat O x M) →
    matLat O ((x.map σ)ᵀ * x) M = M := by sorry
