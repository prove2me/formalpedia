-- Prove2me | Theorems.Thm_GlobalTheory_T_mem_symplecticLieAlgebra_of_exp_smul_mem_symplecticGroup
-- name    : GlobalTheory.T.mem_symplecticLieAlgebra_of_exp_smul_mem_symplecticGroup
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:35:11.857828+00:00
-- url     : https://prove2.me/theorems/3f465625-9cdb-5448-9835-eef913ca62e2
-- title:
--   T: mem symplectic Lie Algebra of exp smul mem symplectic Group
-- statement:
--   The T construction uses the mem symplectic Lie Algebra of exp smul mem symplectic Group property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/MemSymplecticLieAlgebraOfExpSmulMemSymplecticGroStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/MemSymplecticLieAlgebraOfExpSmulMemSymplecticGroStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_MemSymplecticLieAlgebraOfExpSmulMemSymplecticGro
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_MemSymplecticLieAlgebraOfExpSmulMemSymplecticGroStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped Matrix
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.mem_symplecticLieAlgebra_of_exp_smul_mem_symplecticGroup : ∀ (l : Type) [Fintype l] [DecidableEq l] (X : Matrix (l ⊕ l) (l ⊕ l) ℝ), (∀ t : ℝ, NormedSpace.exp (t • X) ∈ Matrix.symplecticGroup l ℝ) → X ∈ LieAlgebra.Symplectic.sp l ℝ := by sorry
