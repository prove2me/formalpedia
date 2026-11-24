-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_NormUnits_isIntegral_of_forall_quot
-- name    : GlobalTheory.UnitLemma.NormUnits.isIntegral_of_forall_quot
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T21:27:07.578905+00:00
-- url     : https://prove2.me/theorems/ff86666d-2e10-4717-9ce3-e8353464b4ac
-- title:
--   Norm Units: is Integral of forall quot
-- statement:
--   The Norm Units construction uses the is Integral of forall quot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FgUnitsQuotIntegralUnitsReducedFiniteAlgebra.lean#L27-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FgUnitsQuotIntegralUnitsReducedFiniteAlgebra.lean#L27-L43

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FgUnitsQuotIntegralUnitsReducedFiniteAlgebra
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
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.NormUnits

theorem GlobalTheory.UnitLemma.NormUnits.isIntegral_of_forall_quot {O A : Type} [CommRing O] [CommRing A] [Algebra O A]
    [IsArtinianRing A] [IsReduced A] (x : A)
    (hx : ∀ I : MaximalSpectrum A, IsIntegral O (Ideal.Quotient.mk I.asIdeal x)) :
    IsIntegral O x := by sorry
