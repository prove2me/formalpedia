-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_CuspVan_extHom_blockUT
-- name    : GlobalTheory.CompanionTheory.TyFin.CuspVan.extHom_blockUT
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T12:16:53.692796+00:00
-- url     : https://prove2.me/theorems/b651d11c-7717-407c-aefd-5736c1b76608
-- title:
--   Cusp Van: ext Hom block UT
-- statement:
--   The Cusp Van construction uses the ext Hom block UT property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CuspidalVanishing.lean#L115-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CuspidalVanishing.lean#L115-L125

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

theorem GlobalTheory.CompanionTheory.TyFin.CuspVan.extHom_blockUT {s s' : ℕ} (b : ι → Fin s) (c : Fin s) (β : ι → Fin s')
    {w : GL {i // b i = c} K}
    (hw : IsBlockUT K (rankMap fun i : {i // b i = c} => β i.1)
      (w : Matrix {i // b i = c} {i // b i = c} K)) :
    IsBlockUT K β (extHom b c w : Matrix ι ι K) := by sorry
