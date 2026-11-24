-- Prove2me | Theorems.Thm_GlobalTheory_RelDimFibCrit_trdeg_affine
-- name    : GlobalTheory.RelDimFibCrit.trdeg_affine
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T19:21:36.530947+00:00
-- url     : https://prove2.me/theorems/0987732f-a131-4c84-b0b3-aed494219ee1
-- title:
--   Rel Dim Fib Crit: trdeg affine
-- statement:
--   The Rel Dim Fib Crit construction uses the trdeg affine property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/SmoothRelativeDimOfTrdeg.lean#L166-L198
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/SmoothRelativeDimOfTrdeg.lean#L166-L198

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
open AlgebraicGeometry CategoryTheory Limits

theorem GlobalTheory.RelDimFibCrit.trdeg_affine {X Y : Scheme.{0}} (f : X ⟶ Y) (U : Y.Opens)
    (hU : IsAffineOpen U) (V : X.Opens) (hV : IsAffineOpen V) (e : V ≤ f ⁻¹ᵁ U)
    (p : PrimeSpectrum Γ(X, V)) :
    @Algebra.trdeg (Y.residueField (f (hV.fromSpec p))) (X.residueField (hV.fromSpec p)) _ _
      (f.residueFieldMap (hV.fromSpec p)).hom.toAlgebra =
    @Algebra.trdeg (p.asIdeal.comap (f.appLE U V e).hom).ResidueField p.asIdeal.ResidueField _ _
      (Ideal.ResidueField.map _ p.asIdeal (f.appLE U V e).hom rfl).toAlgebra := by sorry
