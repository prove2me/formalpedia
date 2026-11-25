-- Prove2me | Theorems.Thm_GlobalTheory_LieCombBaseChange_prod_left_comp
-- name    : GlobalTheory.LieCombBaseChange.prod_left_comp
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T14:34:28.046253+00:00
-- url     : https://prove2.me/theorems/2b9bfb96-6dbd-495a-b88f-c26a82bc3adb
-- title:
--   Lie Comb Base Change: prod left comp
-- statement:
--   The Lie Comb Base Change construction uses the prod left comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/LieCombBaseChange.lean#L43-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/LieCombBaseChange.lean#L43-L80

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasisBaseChange
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_FlagBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AbProj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_LieCombBaseChange
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_Tri_prod

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory GlobalTheory.LieCombBaseChange
variable {R R' : Type} [CommRing R] [CommRing R']

theorem GlobalTheory.LieCombBaseChange.prod_left_comp {S S' : Scheme.{0}} {f : S' ⟶ S} {G : Over S} [GrpObj G] {G' : Over S'} [GrpObj G']
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) {T : Over S} {T' : Over S'} (d : T'.left ⟶ T.left)
    (hd : d ≫ T.hom = T'.hom ≫ f) {n : ℕ} (u : Fin n → (T ⟶ G)) (u' : Fin n → (T' ⟶ G'))
    (hu : ∀ i, (u' i).left ≫ φ = d ≫ (u i).left) :
    (List.ofFn u').prod.left ≫ φ = d ≫ (List.ofFn u).prod.left := by sorry
