-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_CayleyCase_separable_of_adjoin
-- name    : GlobalTheory.UnitLemma.CayleyCase.separable_of_adjoin
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T00:50:57.365826+00:00
-- url     : https://prove2.me/theorems/45e5f522-e912-4a47-b509-d48c384ce1aa
-- title:
--   Cayley Case: separable of adjoin
-- statement:
--   The Cayley Case construction uses the separable of adjoin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnitLemmaResiduallyUnipotentViaCayley.lean#L147-L153
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnitLemmaResiduallyUnipotentViaCayley.lean#L147-L153

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

theorem GlobalTheory.UnitLemma.CayleyCase.separable_of_adjoin {E A : Type} [Field E] [CharZero E] [CommRing A] [Algebra E A] [Module.Finite E A]
    (g Y : A) (h₁ : Y ∈ Algebra.adjoin E ({g} : Set A)) (h₂ : g ∈ Algebra.adjoin E ({Y} : Set A))
    (hg : (LinearMap.mulLeft E g).charpoly.Separable) : (LinearMap.mulLeft E Y).charpoly.Separable := by sorry
