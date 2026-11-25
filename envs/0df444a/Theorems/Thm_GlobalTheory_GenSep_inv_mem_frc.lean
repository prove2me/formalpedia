-- Prove2me | Theorems.Thm_GlobalTheory_GenSep_inv_mem_frc
-- name    : GlobalTheory.GenSep.inv_mem_frc
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T17:25:54.09854+00:00
-- url     : https://prove2.me/theorems/21d1223f-173c-5f6d-96f7-5da5b1799f3d
-- title:
--   Gen Sep: inv mem frc
-- statement:
--   The Gen Sep construction uses the inv mem frc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/AlgebraMapMemMax.lean#L252-L258
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/AlgebraMapMemMax.lean#L252-L258

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_IsUnitOfValEqZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_WeakApprox
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AlgebraicCurves_PlacesRestrictInjective
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_LocalIntegralPolynomials_ExistsValuationAdaptedIndex
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_OneLtAbsNormReal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_AlgebraMapMemMax
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.T0 IsLocalRing MvPolynomial
noncomputable section
open GlobalTheory GlobalTheory.GenSep
variable {Ω F F' : Type} [Field Ω] [Field F] [Field F'] (w : AddValuation F (WithTop ℤ))
  (w' : AddValuation F' (WithTop ℤ)) (ι : Ω →+* F) (ι' : Ω →+* F')

theorem GlobalTheory.GenSep.inv_mem_frc (A : Subring (F × F')) {y : F} {y' : F'} (h : (y, y') ∈ frc A) (hy : y ≠ 0) (hy' : y' ≠ 0) :
    (y⁻¹, y'⁻¹) ∈ frc A := by sorry
