-- Prove2me | Theorems.Thm_GlobalTheory_T_cuspidal_label_unique
-- name    : GlobalTheory.T.cuspidal_label_unique
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:34:24.410247+00:00
-- url     : https://prove2.me/theorems/d0539edd-880a-4c84-8e36-9e0cbea0eea3
-- title:
--   T: cuspidal label unique
-- statement:
--   The T construction uses the cuspidal label unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CuspidalLabelUniqueStatement.lean#L8-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CuspidalLabelUniqueStatement.lean#L8-L10

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CuspidalLabelUnique
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CuspidalLabelUniqueStatement
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

theorem GlobalTheory.T.cuspidal_label_unique : ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (C : LabelConv K) (ι : Type) [Fintype ι] [DecidableEq ι] (τ : FDRep ℂ (GL ι K)) (P P' : K[X]),
    HasCuspLabel C τ P → HasCuspLabel C τ P' → P = P' := by sorry
