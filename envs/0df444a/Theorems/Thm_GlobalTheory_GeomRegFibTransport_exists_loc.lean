-- Prove2me | Theorems.Thm_GlobalTheory_GeomRegFibTransport_exists_loc
-- name    : GlobalTheory.GeomRegFibTransport.exists_loc
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T13:55:53.287891+00:00
-- url     : https://prove2.me/theorems/6093a995-d305-41c4-8ef5-1ecfd30b2cbf
-- title:
--   Geom Reg Fib Transport: exists loc
-- statement:
--   The Geom Reg Fib Transport construction uses the exists loc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/GeomRegFibAdicCompletionOfEssFiniteTypeInt.lean#L8-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/GeomRegFibAdicCompletionOfEssFiniteTypeInt.lean#L8-L22

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

theorem GlobalTheory.GeomRegFibTransport.exists_loc (A : Type) [CommRing A] [IsLocalRing A] [Algebra.EssFiniteType ℤ A] :
    ∃ (A₀ : Type) (_ : CommRing A₀) (_ : Algebra.FiniteType ℤ A₀) (p : Ideal A₀) (_ : p.IsPrime),
      Nonempty (Localization.AtPrime p ≃+* A) := by sorry
