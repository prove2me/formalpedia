-- Prove2me | Theorems.Thm_GlobalTheory_T_unitaryActHermitianBlock_diagOne_liftLastBasis
-- name    : GlobalTheory.T.unitaryActHermitianBlock_diagOne_liftLastBasis
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:40:31.913286+00:00
-- url     : https://prove2.me/theorems/1c71945e-387f-5273-91bd-52721f176f57
-- title:
--   T: unitary Act Hermitian Block diag One lift Last Basis
-- statement:
--   The T construction uses the unitary Act Hermitian Block diag One lift Last Basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnitaryActHermitianBlockDiagOneLiftLastBasisStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnitaryActHermitianBlockDiagOneLiftLastBasisStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitaryActHermitianBlockDiagOneLiftLastBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FullToGlIsSelfAdjoint
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitaryActHermitianBlockDiagOneLiftLastBasisStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.unitaryActHermitianBlock_diagOne_liftLastBasis : ∀ {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] {r : ℕ} (s : Matrix.unitaryGroup (Fin r) E) (X : Hn r F E) (ν : E) (l : F), actU (GlobalTheory.JR.Step.uEmb r E s) (GlobalTheory.JR.Step.liftH X ν l) = GlobalTheory.JR.Step.liftH (actU s X) ν l := by sorry
