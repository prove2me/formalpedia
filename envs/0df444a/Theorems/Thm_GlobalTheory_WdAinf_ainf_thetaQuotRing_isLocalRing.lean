-- Prove2me | Theorems.Thm_GlobalTheory_WdAinf_ainf_thetaQuotRing_isLocalRing
-- name    : GlobalTheory.WdAinf.ainf_thetaQuotRing_isLocalRing
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T16:52:20.267423+00:00
-- url     : https://prove2.me/theorems/05874e00-8e3e-5b32-b035-bd945097edd4
-- title:
--   Wd Ainf: ainf theta Quot Ring is Local Ring
-- statement:
--   The Wd Ainf construction uses the ainf theta Quot Ring is Local Ring property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ModPToValuationResidueFieldSurjective.lean#L205-L214
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ModPToValuationResidueFieldSurjective.lean#L205-L214

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemOfCompat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ModPToValuationResidueFieldSurjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.WdAinf
open WittVector Ideal
variable (p : ℕ) [hp : Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C]
  {v : Valuation C NNReal} (O : Type) [CommRing O] [Algebra O C]
  [Fact ¬IsUnit (p : O)] [IsAdicComplete (span {(p : O)}) O]
variable (hv : v.Integers O) (ε : PreTilt O p)
  (hε : IsPrimitiveRoot (((frobeniusEquiv (PreTilt O p) p).symm ε).untilt) p)
  (ϖ : PreTilt O p) (hϖ : ϖ.untilt = (p : O))
include hv hε hϖ
omit hϖ

theorem GlobalTheory.WdAinf.ainf_thetaQuotRing_isLocalRing : IsLocalRing (Ainf.R0 p O ε) := by sorry
