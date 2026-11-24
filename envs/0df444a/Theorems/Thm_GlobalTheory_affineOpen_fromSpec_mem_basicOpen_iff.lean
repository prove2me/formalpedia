-- Prove2me | Theorems.Thm_GlobalTheory_affineOpen_fromSpec_mem_basicOpen_iff
-- name    : GlobalTheory.affineOpen_fromSpec_mem_basicOpen_iff
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T22:08:04.335268+00:00
-- url     : https://prove2.me/theorems/13a35693-6764-4eef-9206-e9346636c34f
-- title:
--   Global Theory: affine Open from Spec mem basic Open iff
-- statement:
--   The Global Theory construction uses the affine Open from Spec mem basic Open iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsOpenNbhdSectionFibreIsPreirreducible.lean#L10-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsOpenNbhdSectionFibreIsPreirreducible.lean#L10-L12

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsAffineChartPreirreducibleFiberStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PreirreducibleSpaceTensorOfPullbackStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsBasicOpenFibresPreirreducibleSmoothStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsOpenNbhdSectionFibreIsPreirreducible
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj
open GlobalTheory

theorem GlobalTheory.affineOpen_fromSpec_mem_basicOpen_iff {Y : Scheme.{0}} {U : Y.Opens} (hU : IsAffineOpen U)
    (c : Γ(Y, U)) (P : PrimeSpectrum Γ(Y, U)) : hU.fromSpec P ∈ Y.basicOpen c ↔ c ∉ P.asIdeal := by sorry
