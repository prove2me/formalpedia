-- Prove2me | Theorems.Thm_GlobalTheory_Reg_CellChange_exists_algEquiv_of_generates
-- name    : GlobalTheory.Reg.CellChange.exists_algEquiv_of_generates
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T19:18:35.646326+00:00
-- url     : https://prove2.me/theorems/cb661cec-2fa3-41bf-8f74-395d9c26aac2
-- title:
--   Cell Change: exists alg Equiv of generates
-- statement:
--   The Cell Change construction uses the exists alg Equiv of generates property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/ExistsFlagCoordinatesCellChangeBirational.lean#L12-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/ExistsFlagCoordinatesCellChangeBirational.lean#L12-L55

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_RegularCharts_Reframe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_ExistsLowerMulUpperOfLeadingMinors
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_FrameCharts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_ExistsFlagCoordinatesCellChangeBirational
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.Reg GlobalTheory.Reg.CellChange
open Matrix

theorem GlobalTheory.Reg.CellChange.exists_algEquiv_of_generates {κ ι : Type} [Field κ] [Finite ι] (y : ι → FractionRing (MvPolynomial ι κ))
    (hy : ∀ v, algebraMap (MvPolynomial ι κ) (FractionRing (MvPolynomial ι κ)) (MvPolynomial.X v) ∈
      IntermediateField.adjoin κ (Set.range y)) :
    ∃ e : FractionRing (MvPolynomial ι κ) ≃ₐ[κ] FractionRing (MvPolynomial ι κ),
      ∀ v, e (algebraMap (MvPolynomial ι κ) _ (MvPolynomial.X v)) = y v := by sorry
