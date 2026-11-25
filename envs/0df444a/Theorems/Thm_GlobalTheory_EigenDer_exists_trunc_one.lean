-- Prove2me | Theorems.Thm_GlobalTheory_EigenDer_exists_trunc_one
-- name    : GlobalTheory.EigenDer.exists_trunc_one
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T00:58:33.838622+00:00
-- url     : https://prove2.me/theorems/496a86f6-1751-4f27-9669-b1cf5f1b33ea
-- title:
--   Eigen Der: exists trunc one
-- statement:
--   The Eigen Der construction uses the exists trunc one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/SubstMapAlgebraMap.lean#L39-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/SubstMapAlgebraMap.lean#L39-L53

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThetaPt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_HasSubstAddSqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsToJetEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_IsNilpotentOfMemKerJetTruncR
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueFixedPointOfAdicContraction
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_SubstMapAlgebraMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj MvPowerSeries ReciprocityTheory.ChartRestriction.G.Chart ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.JetSer
open ReciprocityTheory.ChartRestriction.G.Out (rosatiφ rosatiε LPow ThetaGrp IsActOf WeilIs translT GlobalFnsSt)
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Good val sval gs)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.EigenDer
variable {R : Type} [CommRing R]

theorem GlobalTheory.EigenDer.exists_trunc_one {G : Over (Spec (CommRingCat.of R))} {κ : Type} (x : Fam G κ)
    (hx : ∀ m, spMap (jetTruncR R κ m) ≫ x (m + 1) = x m) (n : ℕ) :
    ∃ t : JetR R κ (n + 1) →ₐ[R] JetR R κ 1, (∀ j, t (zR (n + 1) j) = zR 1 j) ∧ spMap t ≫ x (n + 1) = x 1 := by sorry
