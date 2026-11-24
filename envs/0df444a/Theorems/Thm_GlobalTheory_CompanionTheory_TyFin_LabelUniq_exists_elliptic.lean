-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_LabelUniq_exists_elliptic
-- name    : GlobalTheory.CompanionTheory.TyFin.LabelUniq.exists_elliptic
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T12:18:53.993551+00:00
-- url     : https://prove2.me/theorems/d793dd66-269c-4f93-bb10-4e1dc42ddfb9
-- title:
--   Label Uniq: exists elliptic
-- statement:
--   The Label Uniq construction uses the exists elliptic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CuspidalLabelUnique.lean#L209-L242
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CuspidalLabelUnique.lean#L209-L242

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_OrthogonalIntVectorsNotAgreeOnRegular
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_RegularIffNatDegreeAndExistsEllipticGL
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_InnerProductRootPowerSumEqOfFrobeniusModEq
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CuspidalLabelUnique
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
open Polynomial CategoryTheory
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TyFin GlobalTheory.CompanionTheory.TyFin.LabelUniq
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

theorem GlobalTheory.CompanionTheory.TyFin.LabelUniq.exists_elliptic (C : LabelConv K) {ι : Type} [Fintype ι] [DecidableEq ι]
    (hd : 0 < Fintype.card ι) (j : ℕ)
    (hj : ∀ e, 0 < e → e < Fintype.card ι →
      ¬ j * Fintype.card K ^ e ≡ j [MOD Fintype.card K ^ Fintype.card ι - 1]) :
    ∃ γ : GL ι K, Irreducible (Matrix.charpoly (γ : Matrix ι ι K)) ∧
      aeval (C.gen (Fintype.card ι) ^ j) (Matrix.charpoly (γ : Matrix ι ι K)) = 0 := by sorry
