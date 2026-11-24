-- Prove2me | Theorems.Thm_GlobalTheory_GeomRegFibTransport_regular_transfer
-- name    : GlobalTheory.GeomRegFibTransport.regular_transfer
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T13:55:39.266813+00:00
-- url     : https://prove2.me/theorems/d4f18d56-e9f7-46d9-909f-deddb5c15dd3
-- title:
--   Geom Reg Fib Transport: regular transfer
-- statement:
--   The Geom Reg Fib Transport construction uses the regular transfer property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/GeomRegFibAdicCompletionOfEssFiniteTypeInt.lean#L186-L194
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/GeomRegFibAdicCompletionOfEssFiniteTypeInt.lean#L186-L194

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

theorem GlobalTheory.GeomRegFibTransport.regular_transfer {T T' : Type} [CommRing T] [CommRing T'] (F : T ≃+* T')
    (hN : IsNoetherianRing T)
    (hR : ∀ (Q : Ideal T) [Q.IsPrime], IsRegularLocalRing (Localization.AtPrime Q)) :
    IsNoetherianRing T' ∧
      ∀ (Q' : Ideal T') [Q'.IsPrime], IsRegularLocalRing (Localization.AtPrime Q') := by sorry
