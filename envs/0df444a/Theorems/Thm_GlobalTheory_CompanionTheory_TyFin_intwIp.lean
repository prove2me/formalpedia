-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_intwIp
-- name    : GlobalTheory.CompanionTheory.TyFin.intwIp
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T12:19:03.358925+00:00
-- url     : https://prove2.me/theorems/95f1362d-c5be-431e-8604-67c4d608aa22
-- title:
--   Ty Fin: intw Ip
-- statement:
--   The Ty Fin construction uses the intw Ip property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IntertwinerInnerProduct.lean#L27-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IntertwinerInnerProduct.lean#L27-L33

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IntertwinerInnerProduct
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TyFin

theorem GlobalTheory.CompanionTheory.TyFin.intwIp : ReciprocityTheory.Ty.Fin.St.IntwIp := by sorry
