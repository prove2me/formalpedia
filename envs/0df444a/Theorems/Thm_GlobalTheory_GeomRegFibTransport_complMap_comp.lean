-- Prove2me | Theorems.Thm_GlobalTheory_GeomRegFibTransport_complMap_comp
-- name    : GlobalTheory.GeomRegFibTransport.complMap_comp
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T13:55:43.594692+00:00
-- url     : https://prove2.me/theorems/2b89dc47-645c-4ae5-985d-5d70e2e7a484
-- title:
--   Geom Reg Fib Transport: compl Map comp
-- statement:
--   The Geom Reg Fib Transport construction uses the compl Map comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/GeomRegFibAdicCompletionOfEssFiniteTypeInt.lean#L73-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/GeomRegFibAdicCompletionOfEssFiniteTypeInt.lean#L73-L83

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

theorem GlobalTheory.GeomRegFibTransport.complMap_comp {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (e : R →+* S)
    (e' : S →+* T) (I : Ideal R) (J : Ideal S) (K : Ideal T) (h : I.map e ≤ J) (h' : J.map e' ≤ K)
    (x : AdicCompletion I R) :
    complMap e' J K h' (complMap e I J h x) = complMap (e'.comp e) I K
      (by rw [← Ideal.map_map]; exact (Ideal.map_mono h).trans h') x := by sorry
