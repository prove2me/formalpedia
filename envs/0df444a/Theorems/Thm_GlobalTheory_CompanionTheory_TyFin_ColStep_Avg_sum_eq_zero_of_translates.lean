-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_ColStep_Avg_sum_eq_zero_of_translates
-- name    : GlobalTheory.CompanionTheory.TyFin.ColStep.Avg.sum_eq_zero_of_translates
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T12:17:16.818562+00:00
-- url     : https://prove2.me/theorems/35027825-ac64-408a-a50e-a53447271662
-- title:
--   Avg: sum eq zero of translates
-- statement:
--   The Avg construction uses the sum eq zero of translates property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/WhittakerVanishesOfRadicalSums.lean#L14-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/WhittakerVanishesOfRadicalSums.lean#L14-L52

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ColGeR
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_PatternGroupStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_WhittakerVanishesOfRadicalSums
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.Ty.Fin GlobalTheory.CompanionTheory.TyFin.ColStep
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TyFin GlobalTheory.CompanionTheory.TyFin.ColStep GlobalTheory.CompanionTheory.TyFin.ColStep.Avg
open Classical

theorem GlobalTheory.CompanionTheory.TyFin.ColStep.Avg.sum_eq_zero_of_translates {G : Type} [Group G] [Fintype G] (N A : Set G) (h1 : (1 : G) ∈ A)
    (hN : ∀ v ∈ A, ∀ u, u * v ∈ N ↔ u ∈ N) (L χ : G → ℂ)
    (hL : ∀ u ∈ N, ∀ v ∈ A, L (u * v) = L u)
    (hs : ∀ u, (∑ v : G, if v ∈ A then χ (u * v) else 0) = 0) :
    (∑ u : G, if u ∈ N then L u * χ u else 0) = 0 := by sorry
