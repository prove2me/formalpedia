-- Prove2me | Theorems.Thm_GlobalTheory_residueField_isAlgebraic_of_etale
-- name    : GlobalTheory.residueField_isAlgebraic_of_etale
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T23:16:10.220443+00:00
-- url     : https://prove2.me/theorems/8f5ad558-027c-431a-bcbc-bd70ff936219
-- title:
--   Global Theory: residue Field is Algebraic of etale
-- statement:
--   The Global Theory construction uses the residue Field is Algebraic of etale property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ResidueFieldIsAlgebraicOfEtale.lean#L6-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ResidueFieldIsAlgebraicOfEtale.lean#L6-L28

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ResidueFieldIsAlgebraicOfEtale
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits
open GlobalTheory

theorem GlobalTheory.residueField_isAlgebraic_of_etale :
    ∀ {A B : Type} [CommRing A] [CommRing B] (g : A →+* B), g.Etale →
    ∀ (P : Ideal B) [P.IsPrime],
    @Algebra.IsAlgebraic (P.comap g).ResidueField P.ResidueField _ _
      (Ideal.ResidueField.map (P.comap g) P g rfl).toAlgebra := by sorry
