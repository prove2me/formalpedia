-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_CuspVan_extHom_off
-- name    : GlobalTheory.CompanionTheory.TyFin.CuspVan.extHom_off
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T12:17:02.742872+00:00
-- url     : https://prove2.me/theorems/4f89729e-fe25-44e1-aaad-555404dd85d2
-- title:
--   Cusp Van: ext Hom off
-- statement:
--   The Cusp Van construction uses the ext Hom off property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CuspidalVanishing.lean#L139-L142
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CuspidalVanishing.lean#L139-L142

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

theorem GlobalTheory.CompanionTheory.TyFin.CuspVan.extHom_off {s : ℕ} (b : ι → Fin s) (c : Fin s) (v : GL {i // b i = c} K) (i j : ι)
    (hij : b i ≠ b j) : (extHom b c v : Matrix ι ι K) i j = 0 := by sorry
