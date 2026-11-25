-- Prove2me | Theorems.Thm_GlobalTheory_LieChart_univChart_baseChange_of_chart
-- name    : GlobalTheory.LieChart.univChart_baseChange_of_chart
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T14:57:30.436258+00:00
-- url     : https://prove2.me/theorems/09c2186c-c38e-5822-bb11-396f9c15dd13
-- title:
--   Lie Chart: univ Chart base Change of chart
-- statement:
--   The Lie Chart construction uses the univ Chart base Change of chart property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/ExistsAffineLieBasisBaseChange.lean#L101-L188
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/ExistsAffineLieBasisBaseChange.lean#L101-L188

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasisBaseChange
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_FlagBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AbProj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_ExistsAffineLieBasisBaseChange
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_spMap_comp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.LieChart
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Chart
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding spMap spMap_comp
open scoped CategoryTheory.Obj

theorem GlobalTheory.LieChart.univChart_baseChange_of_chart {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R']
    (G : Over (Spec (CommRingCat.of R))) [GrpObj G] (C : Chart G) (n : ℕ) (x : ∀ m : ℕ, sp (R₀ := R) (JetR R (Fin n) m) ⟶ G)
    (hx : IsUnivChart G n x) :
    ∃ x' : ∀ m : ℕ, sp (R₀ := R') (JetR R' (Fin n) m) ⟶ (Over.pullback (fB R R')).obj G,
      IsUnivChart _ n x' ∧ ∀ c : Fin n → R,
        (tvec (x := x') (algebraMap R R' ∘ c)).left ≫ pullback.fst G.hom (fB R R') =
          Spec.map (CommRingCat.ofHom (dualMapR (algebraMap R R'))) ≫ (tvec (x := x) c).left := by sorry
