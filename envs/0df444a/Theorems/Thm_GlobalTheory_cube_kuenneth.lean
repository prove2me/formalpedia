-- Prove2me | Theorems.Thm_GlobalTheory_cube_kuenneth
-- name    : GlobalTheory.cube_kuenneth
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T07:50:19.231869+00:00
-- url     : https://prove2.me/theorems/c00792ea-c33e-43b7-a2b0-f5b6a0b16cbc
-- title:
--   Global Theory: cube kuenneth
-- statement:
--   The Global Theory construction uses the cube kuenneth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/RangeRestrictCompSubtypeOfOrthogonalOfNe.lean#L664-L673
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/RangeRestrictCompSubtypeOfOrthogonalOfNe.lean#L664-L673

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CubeTotalComplexAcyclicOfSlicesInductionOnCard
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_RangeRestrictCompSubtypeOfOrthogonalOfNe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits HomologicalComplex TensorProduct
universe v u
open GlobalTheory
open GlobalTheory.Cube Finset.HasAntidiagonal Module
variable {ι κ : Type} [LinearOrder ι] [LinearOrder κ] [Finite ι] [Finite κ] {K : Type u} [Field K]

theorem GlobalTheory.cube_kuenneth (A : Cube.{v} ι K) (B : Cube.{v} κ K)
    (hA : ∀ p, Module.Finite K ((cubeComplex A).homology p))
    (hB : ∀ q, Module.Finite K ((cubeComplex B).homology q)) (n : ℕ) :
    Module.Finite K ((cubeComplex (extTensor A B)).homology n) ∧
      finrank K ((cubeComplex (extTensor A B)).homology n) = ∑ x ∈ antidiagonal n,
        finrank K ((cubeComplex A).homology x.1) * finrank K ((cubeComplex B).homology x.2) := by sorry
