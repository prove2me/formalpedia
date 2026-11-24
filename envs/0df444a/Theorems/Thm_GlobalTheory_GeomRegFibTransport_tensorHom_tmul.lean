-- Prove2me | Theorems.Thm_GlobalTheory_GeomRegFibTransport_tensorHom_tmul
-- name    : GlobalTheory.GeomRegFibTransport.tensorHom_tmul
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T13:55:53.993034+00:00
-- url     : https://prove2.me/theorems/adb749c6-cfd4-4726-8c7a-e1513e883fa8
-- title:
--   Geom Reg Fib Transport: tensor Hom tmul
-- statement:
--   The Geom Reg Fib Transport construction uses the tensor Hom tmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/GeomRegFibAdicCompletionOfEssFiniteTypeInt.lean#L151-L156
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/GeomRegFibAdicCompletionOfEssFiniteTypeInt.lean#L151-L156

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

theorem GlobalTheory.GeomRegFibTransport.tensorHom_tmul {A A' B B' K : Type} [CommRing A] [CommRing A'] [CommRing B]
    [CommRing B'] [CommRing K] [Algebra A B] [Algebra A' B'] [Algebra A K] [Algebra A' K]
    (e : A →+* A') (f : B →+* B') (hf : ∀ a, f (algebraMap A B a) = algebraMap A' B' (e a))
    (hK : ∀ a, algebraMap A K a = algebraMap A' K (e a)) (b : B) (k : K) :
    tensorHom e f hf hK (b ⊗ₜ k) = f b ⊗ₜ k := by sorry
