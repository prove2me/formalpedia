-- Prove2me | Theorems.Thm_GlobalTheory_LieCombBaseChange_dualMap_over
-- name    : GlobalTheory.LieCombBaseChange.dualMap_over
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T14:32:28.447493+00:00
-- url     : https://prove2.me/theorems/b6e470e1-b63a-4268-a024-278084813e3d
-- title:
--   Lie Comb Base Change: dual Map over
-- statement:
--   The Lie Comb Base Change construction uses the dual Map over property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/LieCombBaseChange.lean#L28-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/LieCombBaseChange.lean#L28-L34

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
open GlobalTheory GlobalTheory.LieCombBaseChange
variable {R R' : Type} [CommRing R] [CommRing R']

theorem GlobalTheory.LieCombBaseChange.dualMap_over (f : R →+* R') :
    spMap (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR f) ≫ (epsR R).hom = (epsR R').hom ≫ spMap f := by sorry
