-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_LabelUniq_pow_card_pow_self
-- name    : GlobalTheory.CompanionTheory.TyFin.LabelUniq.pow_card_pow_self
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:27:08.038978+00:00
-- url     : https://prove2.me/theorems/e35f0fb8-12bb-4e60-a166-b022fa63c105
-- title:
--   Label Uniq: pow card pow self
-- statement:
--   The Label Uniq construction uses the pow card pow self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CuspidalLabelUnique.lean#L21-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CuspidalLabelUnique.lean#L21-L35

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

theorem GlobalTheory.CompanionTheory.TyFin.LabelUniq.pow_card_pow_self (x : AlgebraicClosure K) {d : ℕ} (hd : (minpoly K x).natDegree = d) :
    x ^ (Fintype.card K ^ d) = x := by sorry
