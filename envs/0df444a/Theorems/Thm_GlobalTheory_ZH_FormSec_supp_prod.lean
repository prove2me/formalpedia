-- Prove2me | Theorems.Thm_GlobalTheory_ZH_FormSec_supp_prod
-- name    : GlobalTheory.ZH.FormSec.supp_prod
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T22:03:25.356055+00:00
-- url     : https://prove2.me/theorems/ba6d42ce-6c9f-44c4-8105-05fdf2178b6b
-- title:
--   Form Sec: supp prod
-- statement:
--   The Form Sec construction uses the supp prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsFormSec.lean#L50-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsFormSec.lean#L50-L58

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

theorem GlobalTheory.ZH.FormSec.supp_prod {J : Type} {x : J → AddMonoidAlgebra A X} {S : Set X}
    (hx : ∀ i, ((x i).coeff.support : Set X) ⊆ S) (n : J → ℕ) (t : Finset J) :
    ((∏ i ∈ t, x i ^ n i).coeff.support : Set X) ⊆ (∑ i ∈ t, n i) • S := by sorry
