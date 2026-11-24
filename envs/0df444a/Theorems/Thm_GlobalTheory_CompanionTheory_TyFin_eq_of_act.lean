-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_eq_of_act
-- name    : GlobalTheory.CompanionTheory.TyFin.eq_of_act
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T12:19:14.762103+00:00
-- url     : https://prove2.me/theorems/56748829-7571-4a38-ab2a-13472190fd97
-- title:
--   Ty Fin: eq of act
-- statement:
--   The Ty Fin construction uses the eq of act property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CentralIdempotentProperties.lean#L30-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CentralIdempotentProperties.lean#L30-L33

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

theorem GlobalTheory.CompanionTheory.TyFin.eq_of_act (x y : MonoidAlgebra ℂ Γ)
    (h : ∀ τ : FDRep ℂ Γ, Simple τ → Representation.asAlgebraHom τ.ρ x = Representation.asAlgebraHom τ.ρ y) :
    x = y := by sorry
