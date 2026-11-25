-- Prove2me | Theorems.Thm_GlobalTheory_Cube_exists_contraction
-- name    : GlobalTheory.Cube.exists_contraction
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T07:37:26.014129+00:00
-- url     : https://prove2.me/theorems/14b8d1e0-f67a-4e35-986f-5ad81dae02a1
-- title:
--   Cube: exists contraction
-- statement:
--   The Cube construction uses the exists contraction property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/RangeRestrictCompSubtypeOfOrthogonalOfNe.lean#L240-L304
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/RangeRestrictCompSubtypeOfOrthogonalOfNe.lean#L240-L304

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
variable {ι : Type} [LinearOrder ι] {K : Type u} [Field K]
open GlobalTheory.Cube

theorem GlobalTheory.Cube.exists_contraction (A : Cube.{v} ι K) : ∃ e h : Module.End K (∀ s, A.obj s),
    1 - e = (totalD A : Module.End K _) * h + h * totalD A ∧
    (totalD A : Module.End K _) * e = 0 ∧ e * totalD A = 0 ∧ e * e = e ∧
    (∀ p, degProj A p * e = e * degProj A p) ∧ degSign A * e = e * degSign A ∧
    degSign A * h = -(h * degSign A) := by sorry
