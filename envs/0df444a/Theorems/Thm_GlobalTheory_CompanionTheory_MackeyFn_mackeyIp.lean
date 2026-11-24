-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_MackeyFn_mackeyIp
-- name    : GlobalTheory.CompanionTheory.MackeyFn.mackeyIp
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T11:52:26.54392+00:00
-- url     : https://prove2.me/theorems/34a618b5-4ce6-4790-ad60-e41240f5a961
-- title:
--   Mackey Fn: mackey Ip
-- statement:
--   The Mackey Fn construction uses the mackey Ip property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/MackeyInnerProduct.lean#L149-L187
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/MackeyInnerProduct.lean#L149-L187

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MackeyInnerProduct
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.Ty.Fin
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.MackeyFn
variable {Γ : Type} [Group Γ] [Fintype Γ]

theorem GlobalTheory.CompanionTheory.MackeyFn.mackeyIp : ReciprocityTheory.Ty.Fin.St.MackeyIp := by sorry
