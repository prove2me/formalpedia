-- Prove2me | Theorems.Thm_GlobalTheory_RelDimFibCrit_trdeg_residueFieldMap_openImmersion_square
-- name    : GlobalTheory.RelDimFibCrit.trdeg_residueFieldMap_openImmersion_square
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:19:51.361198+00:00
-- url     : https://prove2.me/theorems/f9425795-cfbb-5ee5-849c-a471e8b4a490
-- title:
--   Rel Dim Fib Crit: trdeg residue Field Map open Immersion square
-- statement:
--   The Rel Dim Fib Crit construction uses the trdeg residue Field Map open Immersion square property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/SmoothRelativeDimOfTrdeg.lean#L83-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/SmoothRelativeDimOfTrdeg.lean#L83-L110

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_TrdegResidueFieldEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ResidueFieldIsAlgebraicOfEtale
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ResidueFieldIsoInvCompSpec
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_SmoothRelativeDimOfTrdeg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits
open GlobalTheory GlobalTheory.RelDimFibCrit

theorem GlobalTheory.RelDimFibCrit.trdeg_residueFieldMap_openImmersion_square :
    ∀ {X Y X' Y' : Scheme.{0}} (g : X' ⟶ Y') (f : X ⟶ Y) (jX : X' ⟶ X) (jY : Y' ⟶ Y)
    [IsOpenImmersion jX] [IsOpenImmersion jY], g ≫ jY = jX ≫ f → ∀ x : X',
    @Algebra.trdeg (Y.residueField (f (jX x))) (X.residueField (jX x)) _ _
      (f.residueFieldMap (jX x)).hom.toAlgebra =
    @Algebra.trdeg (Y'.residueField (g x)) (X'.residueField x) _ _
      (g.residueFieldMap x).hom.toAlgebra := by sorry
