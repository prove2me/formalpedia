-- Prove2me | Theorems.Thm_GlobalTheory_UTrans_ReflChar0_exists_inv
-- name    : GlobalTheory.UTrans.ReflChar0.exists_inv
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T02:58:06.159414+00:00
-- url     : https://prove2.me/theorems/802c7c95-1e1c-45df-876a-947d7ac04fa5
-- title:
--   Refl Char0: exists inv
-- statement:
--   The Refl Char0 construction uses the exists inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/UnitaryGeneratedByQuasiReflectionsAndWitt.lean#L129-L151
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/UnitaryGeneratedByQuasiReflectionsAndWitt.lean#L129-L151

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermHyperbolic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_TransvectionIdentitiesUnitary
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsOrthogonalBasisDotProductApplyEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnitaryGeneratedByQuasiReflectionsAndWitt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped Matrix
open GlobalTheory GlobalTheory.UTrans GlobalTheory.UTrans.ReflChar0
open GlobalTheory.UTrans.Calc
variable {E : Type} [Field E] {n : ℕ} {σ : E →+* E} {G : Matrix (Fin n) (Fin n) E}

theorem GlobalTheory.UTrans.ReflChar0.exists_inv (hG : IsHerm σ G) (l : List ((Fin n → E) × E))
    (hl : ∀ p ∈ l, hf σ G p.1 p.1 ≠ 0 ∧ p.2 * σ p.2 = 1) :
    ∃ l' : List ((Fin n → E) × E), (∀ p ∈ l', hf σ G p.1 p.1 ≠ 0 ∧ p.2 * σ p.2 = 1) ∧
      (l'.map fun p => tv σ G p.1 ((p.2 - 1) / hf σ G p.1 p.1)).prod *
        (l.map fun p => tv σ G p.1 ((p.2 - 1) / hf σ G p.1 p.1)).prod = 1 := by sorry
