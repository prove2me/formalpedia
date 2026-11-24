-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_zIdem_act
-- name    : GlobalTheory.CompanionTheory.TyFin.zIdem_act
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T12:19:46.668899+00:00
-- url     : https://prove2.me/theorems/c591097c-be7b-4c2d-b78f-2c5b7607cabe
-- title:
--   Ty Fin: z Idem act
-- statement:
--   The Ty Fin construction uses the z Idem act property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CentralIdempotentProperties.lean#L22-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CentralIdempotentProperties.lean#L22-L28

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CentralIdempotentAction
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SeparableIrreducibleStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SimpleIffIrreducibleStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CentralIdempotentProperties
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.Ty.Fin CategoryTheory
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TyFin
variable {Γ : Type} [Group Γ] [Fintype Γ]

theorem GlobalTheory.CompanionTheory.TyFin.zIdem_act (τ σ : FDRep ℂ Γ) (hτ : Simple τ) (hσ : Simple σ) :
    Representation.asAlgebraHom σ.ρ (zIdem τ) = (open Classical in if Nonempty (τ ≅ σ) then 1 else 0) := by sorry
