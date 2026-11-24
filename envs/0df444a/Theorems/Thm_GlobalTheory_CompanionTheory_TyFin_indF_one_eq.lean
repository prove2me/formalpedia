-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_indF_one_eq
-- name    : GlobalTheory.CompanionTheory.TyFin.indF_one_eq
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T19:33:14.246122+00:00
-- url     : https://prove2.me/theorems/dc729f45-037b-48c5-bc77-dcd19fe04971
-- title:
--   Ty Fin: ind F one eq
-- statement:
--   The Ty Fin construction uses the ind F one eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/HarishChandraDimension.lean#L19-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/HarishChandraDimension.lean#L19-L26

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HarishChandraCharacterStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HarishChandraDimension
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.Ty.Fin
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TyFin

theorem GlobalTheory.CompanionTheory.TyFin.indF_one_eq {Γ : Type} [Group Γ] [Fintype Γ] (H : Subgroup Γ) (φ : Γ → ℂ) :
    indF H φ 1 = (Nat.card H : ℂ)⁻¹ * ((Nat.card Γ : ℂ) * φ 1) := by sorry
