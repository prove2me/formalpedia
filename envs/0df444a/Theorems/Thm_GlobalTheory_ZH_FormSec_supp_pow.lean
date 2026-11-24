-- Prove2me | Theorems.Thm_GlobalTheory_ZH_FormSec_supp_pow
-- name    : GlobalTheory.ZH.FormSec.supp_pow
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T22:01:47.679775+00:00
-- url     : https://prove2.me/theorems/419e71ff-8035-4902-94d9-5b72d9f26ef1
-- title:
--   Form Sec: supp pow
-- statement:
--   The Form Sec construction uses the supp pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsFormSec.lean#L44-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsFormSec.lean#L44-L48

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

theorem GlobalTheory.ZH.FormSec.supp_pow {x : AddMonoidAlgebra A X} {S : Set X} (hx : (x.coeff.support : Set X) ⊆ S) (n : ℕ) :
    ((x ^ n).coeff.support : Set X) ⊆ n • S := by sorry
