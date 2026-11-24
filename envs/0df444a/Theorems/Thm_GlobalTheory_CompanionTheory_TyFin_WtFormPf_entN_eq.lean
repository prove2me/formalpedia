-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_WtFormPf_entN_eq
-- name    : GlobalTheory.CompanionTheory.TyFin.WtFormPf.entN_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:11:15.715041+00:00
-- url     : https://prove2.me/theorems/1f42ff40-2512-431a-824d-d96b51f4addf
-- title:
--   Wt Form Pf: ent N eq
-- statement:
--   The Wt Form Pf construction uses the ent N eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CardJPat.lean#L20-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CardJPat.lean#L20-L39

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_PatternGroupStatementStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CardJPat
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TyFin GlobalTheory.CompanionTheory.TyFin.WtFormPf
open ReciprocityTheory.Ty.Fin.Lq

theorem GlobalTheory.CompanionTheory.TyFin.WtFormPf.entN_eq {A : Type} [Semiring A] {N : ℕ} (M : Matrix (Fin N) (Fin N) A) (x y : ℕ) :
    entN M x y = ∑ i : Fin N, ∑ j : Fin N, (if (i : ℕ) = x ∧ (j : ℕ) = y then (1 : A) else 0) * M i j := by sorry
