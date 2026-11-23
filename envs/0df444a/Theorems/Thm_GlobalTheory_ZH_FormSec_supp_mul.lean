-- Prove2me | Theorems.Thm_GlobalTheory_ZH_FormSec_supp_mul
-- name    : GlobalTheory.ZH.FormSec.supp_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:09:27.952213+00:00
-- url     : https://prove2.me/theorems/e6c2ca24-44e7-4592-ad45-4734b173b233
-- title:
--   Form Sec: supp mul
-- statement:
--   The Form Sec construction uses the supp mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsFormSec.lean#L32-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsFormSec.lean#L32-L37

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PullChartIsLB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsUnitCharts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_CoeffSymmSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsFormSec
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
noncomputable section
open GlobalTheory GlobalTheory.ZH GlobalTheory.ZH.FormSec
open scoped Pointwise
variable {A X : Type} [CommRing A] [AddCommGroup X]

theorem GlobalTheory.ZH.FormSec.supp_mul {x y : AddMonoidAlgebra A X} {S S' : Set X} (hx : (x.coeff.support : Set X) ⊆ S)
    (hy : (y.coeff.support : Set X) ⊆ S') : ((x * y).coeff.support : Set X) ⊆ S + S' := by sorry
