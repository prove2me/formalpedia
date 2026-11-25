-- Prove2me | Theorems.Thm_GlobalTheory_CurveNorm_exists_lift_of_isIntegral
-- name    : GlobalTheory.CurveNorm.exists_lift_of_isIntegral
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T13:31:25.54503+00:00
-- url     : https://prove2.me/theorems/7bac1c01-6c65-4fbb-b28e-c357775a16cc
-- title:
--   Curve Norm: exists lift of is Integral
-- statement:
--   The Curve Norm construction uses the exists lift of is Integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/ExistsSmoothNormalisation.lean#L7-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/ExistsSmoothNormalisation.lean#L7-L39

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FiniteIntegralClosureOfIsIntegrallyClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_SmoothOfIsDedekindDomain
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExistsSmoothNormalisation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CurveNorm

theorem GlobalTheory.CurveNorm.exists_lift_of_isIntegral {k E E' : Type} [Field k] [IsAlgClosed k] [CommRing E]
    [CommRing E'] [Algebra k E] [Algebra k E'] [Algebra E E'] [IsScalarTower k E E']
    [Algebra.IsIntegral E E'] (hinj : Function.Injective (algebraMap E E')) (e : E →ₐ[k] k) :
    ∃ e' : E' →ₐ[k] k, e'.comp (IsScalarTower.toAlgHom k E E') = e := by sorry
