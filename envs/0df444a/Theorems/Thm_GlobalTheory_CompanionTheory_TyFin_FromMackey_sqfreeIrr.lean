-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_FromMackey_sqfreeIrr
-- name    : GlobalTheory.CompanionTheory.TyFin.FromMackey.sqfreeIrr
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:10:29.222614+00:00
-- url     : https://prove2.me/theorems/6611f841-ecfe-4154-83e8-fe55d6dc7d27
-- title:
--   From Mackey: sqfree Irr
-- statement:
--   The From Mackey construction uses the sqfree Irr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ConsequenceOfMackey.lean#L70-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ConsequenceOfMackey.lean#L70-L78

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

theorem GlobalTheory.CompanionTheory.TyFin.FromMackey.sqfreeIrr (hMk : MackeyCusp K) : SqfreeIrr K := by sorry
