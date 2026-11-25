-- Prove2me | Theorems.Thm_GlobalTheory_Cube_ext_restrictDeg
-- name    : GlobalTheory.Cube.ext_restrictDeg
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T07:40:40.155303+00:00
-- url     : https://prove2.me/theorems/3ef44398-cc63-452d-a676-81b8837ad511
-- title:
--   Cube: ext restrict Deg
-- statement:
--   The Cube construction uses the ext restrict Deg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/RangeRestrictCompSubtypeOfOrthogonalOfNe.lean#L65-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/RangeRestrictCompSubtypeOfOrthogonalOfNe.lean#L65-L67

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
open GlobalTheory.Cube
variable {ι : Type} {R : Type u} [Ring R]

theorem GlobalTheory.Cube.ext_restrictDeg {A : Cube.{v} ι R} {x y : ∀ s, A.obj s}
    (h : ∀ p, restrictDeg A p x = restrictDeg A p y) : x = y := by sorry
