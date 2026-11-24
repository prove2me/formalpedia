-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_CuspVan_extHom_mem_unip
-- name    : GlobalTheory.CompanionTheory.TyFin.CuspVan.extHom_mem_unip
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T12:17:06.003812+00:00
-- url     : https://prove2.me/theorems/3c24f095-4386-48bc-9de4-dcf86a3f5b1e
-- title:
--   Cusp Van: ext Hom mem unip
-- statement:
--   The Cusp Van construction uses the ext Hom mem unip property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CuspidalVanishing.lean#L127-L137
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CuspidalVanishing.lean#L127-L137

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CuspidalVanishing
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TyFin GlobalTheory.CompanionTheory.TyFin.CuspVan
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem GlobalTheory.CompanionTheory.TyFin.CuspVan.extHom_mem_unip {s s' : ℕ} (b : ι → Fin s) (c : Fin s) (β : ι → Fin s')
    {v : GL {i // b i = c} K} (hv : v ∈ unip K (rankMap fun i : {i // b i = c} => β i.1)) :
    extHom b c v ∈ unip K β := by sorry
