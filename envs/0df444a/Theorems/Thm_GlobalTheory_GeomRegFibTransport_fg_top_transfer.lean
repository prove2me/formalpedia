-- Prove2me | Theorems.Thm_GlobalTheory_GeomRegFibTransport_fg_top_transfer
-- name    : GlobalTheory.GeomRegFibTransport.fg_top_transfer
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T13:55:53.391142+00:00
-- url     : https://prove2.me/theorems/6738564b-de64-4b9e-850c-d39af79e5915
-- title:
--   Geom Reg Fib Transport: fg top transfer
-- statement:
--   The Geom Reg Fib Transport construction uses the fg top transfer property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/GeomRegFibAdicCompletionOfEssFiniteTypeInt.lean#L115-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/GeomRegFibAdicCompletionOfEssFiniteTypeInt.lean#L115-L129

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

theorem GlobalTheory.GeomRegFibTransport.fg_top_transfer {F F' K : Type} [Field F] [Field F'] [Field K] [Algebra F K] [Algebra F' K]
    (φ : F ≃+* F') (hφ : ∀ x, algebraMap F K x = algebraMap F' K (φ x))
    (h : (⊤ : IntermediateField F' K).FG) : (⊤ : IntermediateField F K).FG := by sorry
