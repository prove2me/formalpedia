-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_FromMackey_sqfreeUnique
-- name    : GlobalTheory.CompanionTheory.TyFin.FromMackey.sqfreeUnique
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T12:17:42.436172+00:00
-- url     : https://prove2.me/theorems/cd51e363-e193-4c52-a337-1c8aaff8f1b6
-- title:
--   From Mackey: sqfree Unique
-- statement:
--   The From Mackey construction uses the sqfree Unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ConsequenceOfMackey.lean#L80-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ConsequenceOfMackey.lean#L80-L98

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MaschkeProperties
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CuspidalIsomorphismProperties
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SimpleIffIrreducible
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ConsequenceOfMackey
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory ReciprocityTheory.Ty.Fin
open Formalism.IrreducibleCountingLemmas.TYPES hiding zIdem IsCuspidal
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TyFin GlobalTheory.CompanionTheory.TyFin.FromMackey
variable (K : Type) [Field K] [Fintype K] [DecidableEq K]
variable {K}

theorem GlobalTheory.CompanionTheory.TyFin.FromMackey.sqfreeUnique (hMk : MackeyCusp K) : SqfreeUnique K := by sorry
