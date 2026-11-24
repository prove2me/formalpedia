-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_KrullLocal_exists_ringHom_of_fractions
-- name    : GlobalTheory.CompanionTheory.KrullLocal.exists_ringHom_of_fractions
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T11:52:33.115688+00:00
-- url     : https://prove2.me/theorems/041432db-42c8-4b1c-9554-62c3c1227093
-- title:
--   Krull Local: exists ring Hom of fractions
-- statement:
--   The Krull Local construction uses the exists ring Hom of fractions property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/TensorPrimeLocalizationCriterion.lean#L6-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/TensorPrimeLocalizationCriterion.lean#L6-L88

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_TensorPrimeLocalizationCriterion
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.KrullLocal

theorem GlobalTheory.CompanionTheory.KrullLocal.exists_ringHom_of_fractions {B C D : Type} [CommRing B] [CommRing C] [CommRing D]
    [Algebra B C] (q : Ideal C) [hq : q.IsPrime] (φ : B →+* D)
    (hu : ∀ t : B, algebraMap B C t ∉ q → IsUnit (φ t))
    (h1 : ∀ c : C, ∃ b t : B, algebraMap B C t ∉ q ∧ ∃ v : C, v ∉ q ∧
      v * (algebraMap B C t * c) = v * algebraMap B C b)
    (h2 : ∀ b : B, (∃ v : C, v ∉ q ∧ v * algebraMap B C b = 0) → φ b = 0) :
    ∃ g : C →+* D, (∀ b, g (algebraMap B C b) = φ b) ∧ ∀ v, v ∉ q → IsUnit (g v) := by sorry
