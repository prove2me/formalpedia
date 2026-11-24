-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_TyFinSamePart_avg_of_surjective
-- name    : GlobalTheory.CompanionTheory.TyFinSamePart.avg_of_surjective
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T12:18:14.222396+00:00
-- url     : https://prove2.me/theorems/8cf5bc66-60a2-40fd-9a6e-564818846ee1
-- title:
--   Ty Fin Same Part: avg of surjective
-- statement:
--   The Ty Fin Same Part construction uses the avg of surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SamePartitionStatement.lean#L11-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SamePartitionStatement.lean#L11-L31

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SamePartitionStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.Ty.Fin
open Formalism.IrreducibleCountingLemmas.TYPES hiding zIdem IsCuspidal
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TyFinSamePart

theorem GlobalTheory.CompanionTheory.TyFinSamePart.avg_of_surjective {G Q : Type} [Group G] [Group Q] [Fintype G] [Fintype Q]
    (f : G →* Q) (hf : Function.Surjective f) (F : Q → ℂ) :
    (Fintype.card G : ℂ)⁻¹ * ∑ g, F (f g) = (Fintype.card Q : ℂ)⁻¹ * ∑ q, F q := by sorry
