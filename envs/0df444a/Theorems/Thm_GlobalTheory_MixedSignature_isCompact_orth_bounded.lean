-- Prove2me | Theorems.Thm_GlobalTheory_MixedSignature_isCompact_orth_bounded
-- name    : GlobalTheory.MixedSignature.isCompact_orth_bounded
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T14:54:36.650516+00:00
-- url     : https://prove2.me/theorems/14910354-c4b3-468c-bb12-f181e0437fdb
-- title:
--   Mixed Signature: is Compact orth bounded
-- statement:
--   The Mixed Signature construction uses the is Compact orth bounded property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/OrthonormalFramesBoundedOfDefinite.lean#L295-L319
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/OrthonormalFramesBoundedOfDefinite.lean#L295-L319

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspidalExponentialDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IntegralBasisReduction
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_HermitianLatticeMaps
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_DetNeZeroOfIsOrth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_FinMuOfFiniteCovolume
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsIntMulIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_MahlerCompactness
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsStabiliserImageSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_OrthonormalFramesBoundedOfDefinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_IsOrthUpdateMulInv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_FrameStepOfRightMulRealUnitaryGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_OrthonormalFramesBoundedOfDefinite
import Theorems.Thm_GlobalTheory_FiniteCovolume_embGL_val
import Theorems.Thm_GlobalTheory_FiniteCovolume_hermC_eq_dotProduct
import Theorems.Thm_GlobalTheory_FiniteCovolume_inv_keeps_gram
import Theorems.Thm_GlobalTheory_FlagMahler_finite_bounded
import Theorems.Thm_GlobalTheory_IntegralMultiples_exists_int_smul_mem
import Theorems.Thm_GlobalTheory_LatFin_exists_common_den
import Theorems.Thm_GlobalTheory_LatFin_exists_int_smul_mem
import Theorems.Thm_GlobalTheory_LatFin_finite_bounded
import Theorems.Thm_GlobalTheory_UnitaryFrames_hermC_eq_dot
import Theorems.Thm_GlobalTheory_UnitaryFrames_hermC_mulVec
import Theorems.Thm_GlobalTheory_UnitaryFrames_locallyCompact_GL
import Theorems.Thm_GlobalTheory_UnitaryFrames_secondCountable_GL
import Theorems.Thm_GlobalTheory_UnitaryLift_det_ne_zero_of_diag
import Theorems.Thm_P2M_GlobalTheory_UnitaryFrames_col_mul__08ccc1f94cd1

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix ComplexConjugate
open GlobalTheory GlobalTheory.MixedSignature
open GlobalTheory.UnitaryFrames (hermC_eq_dot gram_eq_mul hermC_mulVec col_mul' locallyCompact_GL secondCountable_GL)
open GlobalTheory.FiniteCovolume (inv_keeps_gram embGL embGL_val hermC_eq_dotProduct uStabSubgroup)
open GlobalTheory.UnitaryLift (det_ne_zero_of_diag)
open GlobalTheory.LatFin (exists_common_den exists_int_smul_mem finite_bounded)
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem GlobalTheory.MixedSignature.isCompact_orth_bounded :
    (∀ (r : ℕ) (X : Data E r) (G : Matrix (Fin r) (Fin r) E) (p : X.Ψ → ℕ) (R : ℝ),
      IsCompact {x : Frame X.Ψ r | Orth X G p x ∧ ∀ τ a b, ‖x τ a b‖ ≤ R}) := by sorry
