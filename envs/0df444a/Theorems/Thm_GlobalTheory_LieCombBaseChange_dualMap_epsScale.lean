-- Prove2me | Theorems.Thm_GlobalTheory_LieCombBaseChange_dualMap_epsScale
-- name    : GlobalTheory.LieCombBaseChange.dualMap_epsScale
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T14:43:25.253554+00:00
-- url     : https://prove2.me/theorems/b23ba770-21e2-45dc-93b9-0041c5225368
-- title:
--   Lie Comb Base Change: dual Map eps Scale
-- statement:
--   The Lie Comb Base Change construction uses the dual Map eps Scale property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/LieCombBaseChange.lean#L20-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/LieCombBaseChange.lean#L20-L26

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

theorem GlobalTheory.LieCombBaseChange.dualMap_epsScale (f : R →+* R') (c : R) :
    spMap (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR f) ≫ spMap (epsScaleR c) =
      spMap (epsScaleR (f c)) ≫ spMap (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR f) := by sorry
