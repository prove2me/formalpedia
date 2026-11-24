-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_LabelUniq_exists_root
-- name    : GlobalTheory.CompanionTheory.TyFin.LabelUniq.exists_root
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T12:21:10.198744+00:00
-- url     : https://prove2.me/theorems/48f4549f-ac3a-4d7c-bc92-fe63df174773
-- title:
--   Label Uniq: exists root
-- statement:
--   The Label Uniq construction uses the exists root property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CuspidalLabelUnique.lean#L179-L207
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CuspidalLabelUnique.lean#L179-L207

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

theorem GlobalTheory.CompanionTheory.TyFin.LabelUniq.exists_root (C : LabelConv K) {d : ℕ} (hd : 0 < d) {P : K[X]} (hm : P.Monic)
    (hi : Irreducible P) (hX : P ≠ X) (hdeg : P.natDegree = d) :
    ∃ (x : AlgebraicClosure K) (s : ℕ), aeval x P = 0 ∧ minpoly K x = P ∧ C.gen d ^ s = x ∧
      ∀ e, 0 < e → e < d → ¬ s * Fintype.card K ^ e ≡ s [MOD Fintype.card K ^ d - 1] := by sorry
