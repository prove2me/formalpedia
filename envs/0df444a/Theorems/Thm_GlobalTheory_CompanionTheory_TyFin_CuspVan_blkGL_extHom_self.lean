-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_CuspVan_blkGL_extHom_self
-- name    : GlobalTheory.CompanionTheory.TyFin.CuspVan.blkGL_extHom_self
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T12:17:18.176538+00:00
-- url     : https://prove2.me/theorems/85ad200b-27d8-48a1-8722-2ffe7046c51c
-- title:
--   Cusp Van: blk GL ext Hom self
-- statement:
--   The Cusp Van construction uses the blk GL ext Hom self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CuspidalVanishing.lean#L150-L158
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CuspidalVanishing.lean#L150-L158

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

theorem GlobalTheory.CompanionTheory.TyFin.CuspVan.blkGL_extHom_self {s : ℕ} (b : ι → Fin s) (c : Fin s) (v : GL {i // b i = c} K)
    (hp : extHom b c v ∈ parab K b) : blkGL b c (extHom b c v) = v := by sorry
