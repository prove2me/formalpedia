-- Prove2me | Theorems.Thm_GlobalTheory_GeomRegFibTransport_geomRegFib_adicCompletion_of_essFiniteType_int
-- name    : GlobalTheory.GeomRegFibTransport.geomRegFib_adicCompletion_of_essFiniteType_int
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:05:58.109946+00:00
-- url     : https://prove2.me/theorems/d4782978-866a-4562-a1b7-208586df7e87
-- title:
--   Geom Reg Fib Transport: geom Reg Fib adic Completion of ess Finite Type int
-- statement:
--   The Geom Reg Fib Transport construction uses the geom Reg Fib adic Completion of ess Finite Type int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/GeomRegFibAdicCompletionOfEssFiniteTypeInt.lean#L221-L230
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/GeomRegFibAdicCompletionOfEssFiniteTypeInt.lean#L221-L230

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_FinalTheorems
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_GeomRegFibAdicCompletionOfEssFiniteTypeInt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing TensorProduct
open GlobalTheory GlobalTheory.GeomRegFibTransport
open ReciprocityTheory.AnForm.R.FinalTheorems

theorem GlobalTheory.GeomRegFibTransport.geomRegFib_adicCompletion_of_essFiniteType_int :
    (∀ (A : Type) [CommRing A] [Algebra.FiniteType ℤ A], ReciprocityTheory.AnForm.R.FinalTheorems.QERing A) →
      ∀ (A : Type) [CommRing A] [IsLocalRing A] [Algebra.EssFiniteType ℤ A],
        ReciprocityTheory.AnForm.R.FinalTheorems.GeomRegFib A (AdicCompletion (IsLocalRing.maximalIdeal A) A) := by sorry
