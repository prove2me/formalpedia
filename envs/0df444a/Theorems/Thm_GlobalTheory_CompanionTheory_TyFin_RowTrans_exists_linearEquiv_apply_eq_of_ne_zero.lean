-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_RowTrans_exists_linearEquiv_apply_eq_of_ne_zero
-- name    : GlobalTheory.CompanionTheory.TyFin.RowTrans.exists_linearEquiv_apply_eq_of_ne_zero
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T12:18:58.979568+00:00
-- url     : https://prove2.me/theorems/e2609781-d2ca-4449-9710-25d12d72777e
-- title:
--   Row Trans: exists linear Equiv apply eq of ne zero
-- statement:
--   The Row Trans construction uses the exists linear Equiv apply eq of ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/GLTransitiveNonzeroVectors.lean#L9-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/GLTransitiveNonzeroVectors.lean#L9-L20

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ColGeR
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GLTransitiveNonzeroVectors
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.Ty.Fin GlobalTheory.CompanionTheory.TyFin.ColStep
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TyFin GlobalTheory.CompanionTheory.TyFin.RowTrans

theorem GlobalTheory.CompanionTheory.TyFin.RowTrans.exists_linearEquiv_apply_eq_of_ne_zero {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {x y : V} (hx : x ≠ 0) (hy : y ≠ 0) : ∃ e : V ≃ₗ[K] V, e x = y := by sorry
