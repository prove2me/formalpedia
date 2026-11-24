-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_LabelUniq_minpoly_pow_card_pow
-- name    : GlobalTheory.CompanionTheory.TyFin.LabelUniq.minpoly_pow_card_pow
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T12:19:32.472614+00:00
-- url     : https://prove2.me/theorems/7256d3b0-60fa-4f8a-be18-7057f32df29c
-- title:
--   Label Uniq: minpoly pow card pow
-- statement:
--   The Label Uniq construction uses the minpoly pow card pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CuspidalLabelUnique.lean#L46-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CuspidalLabelUnique.lean#L46-L50

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
variable {K : Type} [Field K] [Fintype K]

theorem GlobalTheory.CompanionTheory.TyFin.LabelUniq.minpoly_pow_card_pow (x : AlgebraicClosure K) (i : ℕ) :
    minpoly K (x ^ (Fintype.card K ^ i)) = minpoly K x := by sorry
