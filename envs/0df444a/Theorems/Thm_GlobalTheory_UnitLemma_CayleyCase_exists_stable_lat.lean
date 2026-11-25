-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_CayleyCase_exists_stable_lat
-- name    : GlobalTheory.UnitLemma.CayleyCase.exists_stable_lat
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T00:50:25.173545+00:00
-- url     : https://prove2.me/theorems/632ad798-fcda-4be1-acac-9b25b3355d53
-- title:
--   Cayley Case: exists stable lat
-- statement:
--   The Cayley Case construction uses the exists stable lat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnitLemmaResiduallyUnipotentViaCayley.lean#L99-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnitLemmaResiduallyUnipotentViaCayley.lean#L99-L120

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocalRingOfIdem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CardStableLatticesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AdjoinEqTopAndIsReducedOfCharpolySeparableStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CharpolyMulLeftSeparableOfAdjoinEqTopStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitLemmaResiduallyUnipotentViaCayley
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.UnitLemma Polynomial
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.CayleyCase

theorem GlobalTheory.UnitLemma.CayleyCase.exists_stable_lat {O E A : Type} [CommRing O] [Field E] [CommRing A] [Algebra O E] [Algebra E A]
    [Algebra O A] [IsScalarTower O E A] [Module.Finite E A] (g : A) (hg : IsIntegral O g) :
    ∃ M : Submodule O A, IsLat O E M ∧ ∀ y ∈ M, g * y ∈ M := by sorry
