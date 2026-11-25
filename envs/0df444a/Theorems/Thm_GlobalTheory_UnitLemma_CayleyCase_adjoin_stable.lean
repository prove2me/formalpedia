-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_CayleyCase_adjoin_stable
-- name    : GlobalTheory.UnitLemma.CayleyCase.adjoin_stable
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T00:56:32.119944+00:00
-- url     : https://prove2.me/theorems/981f8c60-826e-4808-a28f-4989f72a0ecf
-- title:
--   Cayley Case: adjoin stable
-- statement:
--   The Cayley Case construction uses the adjoin stable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnitLemmaResiduallyUnipotentViaCayley.lean#L30-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnitLemmaResiduallyUnipotentViaCayley.lean#L30-L37

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocalRingOfIdem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CardStableLatticesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AdjoinEqTopAndIsReducedOfCharpolySeparableStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CharpolyMulLeftSeparableOfAdjoinEqTopStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitLemmaResiduallyUnipotentViaCayley
import Theorems.Thm_GlobalTheory_UnitLemma_Orbit_adjoin_stable

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

theorem GlobalTheory.UnitLemma.CayleyCase.adjoin_stable {O A : Type} [CommRing O] [CommRing A] [Algebra O A] (a : A) (L : Submodule O A)
    (hL : ∀ y ∈ L, a * y ∈ L) : ∀ z ∈ Algebra.adjoin O ({a} : Set A), ∀ y ∈ L, z * y ∈ L := by sorry
