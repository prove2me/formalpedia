-- Prove2me | Theorems.Thm_GlobalTheory_ThetaRational_algHom_apply_mv
-- name    : GlobalTheory.ThetaRational.algHom_apply_mv
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T21:05:55.714858+00:00
-- url     : https://prove2.me/theorems/7ffb7486-b934-4286-a869-65f4a557d85d
-- title:
--   Theta Rational: alg Hom apply mv
-- statement:
--   The Theta Rational construction uses the alg Hom apply mv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/IsIntegralAndRationalTheta.lean#L224-L227
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/IsIntegralAndRationalTheta.lean#L224-L227

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_IsIntegralAndRationalTheta
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.PTheta Complex Matrix Filter Topology
open scoped BigOperators Real ContDiff
open GlobalTheory GlobalTheory.ThetaRational
variable {A : Type*} [CommRing A] [Algebra ℂ A] {n : ℕ}

theorem GlobalTheory.ThetaRational.algHom_apply_mv (j : MvPolynomial (Fin n) ℂ →ₐ[ℂ] A) (χ : A →ₐ[ℂ] ℂ)
    (q : MvPolynomial (Fin n) ℂ) :
    χ (j q) = MvPolynomial.eval (fun i => χ (j (MvPolynomial.X i))) q := by sorry
