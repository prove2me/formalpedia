-- Prove2me | Theorems.Thm_GlobalTheory_lieComb_baseChange
-- name    : GlobalTheory.lieComb_baseChange
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T14:31:57.963633+00:00
-- url     : https://prove2.me/theorems/a175db6f-f9dc-43a1-848e-23e5a4ecd38a
-- title:
--   Global Theory: lie Comb base Change
-- statement:
--   The Global Theory construction uses the lie Comb base Change property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/LieCombBaseChange.lean#L88-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/LieCombBaseChange.lean#L88-L116

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasisBaseChange
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_FlagBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AbProj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_LieCombBaseChange
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
open GlobalTheory
open LieCombBaseChange

theorem GlobalTheory.lieComb_baseChange : ∀ (R R' : Type) [CommRing R] [CommRing R'] (f : R →+* R') (G : Over (Sp R)) [GrpObj G] (G' : Over (Sp R')) [GrpObj G'] (φ : G'.left ⟶ G.left), IsGrpPullback G' G (spMap f) φ → ∀ (n : ℕ) (v : Fin n → (epsR R ⟶ G)) (w : epsR R ⟶ G) (a : Fin n → R) (v' : Fin n → (epsR R' ⟶ G')) (w' : epsR R' ⟶ G'), (∀ j, (v' j).left ≫ φ = spMap (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR f) ≫ (v j).left) → IsLieComb a v w → (w'.left ≫ φ = spMap (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR f) ≫ w.left ↔ IsLieComb (fun i => f (a i)) v' w') := by sorry
