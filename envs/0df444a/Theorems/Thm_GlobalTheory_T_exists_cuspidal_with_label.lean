-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_cuspidal_with_label
-- name    : GlobalTheory.T.exists_cuspidal_with_label
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T02:36:26.006321+00:00
-- url     : https://prove2.me/theorems/ff746e7c-59c3-4ab6-99b9-746f082cc66a
-- title:
--   T: exists cuspidal with label
-- statement:
--   The T construction uses the exists cuspidal with label property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsCuspidalWithLabelStatement.lean#L8-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsCuspidalWithLabelStatement.lean#L8-L10

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsCuspidalWithLabel
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsCuspidalWithLabelStatement
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
open Polynomial CategoryTheory
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_cuspidal_with_label : ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (C : LabelConv K) (d : ℕ), 1 ≤ d → ∀ P : K[X], P.Monic → Irreducible P → P ≠ X → P.natDegree = d →
    ∃ τ : FDRep ℂ (GL (Fin d) K), Simple τ ∧ IsCuspidal K τ ∧ HasCuspLabel C τ P := by sorry
