-- Prove2me | Theorems.Thm_GlobalTheory_LocalInv_matches_chi
-- name    : GlobalTheory.LocalInv.matches_chi
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T19:24:04.952815+00:00
-- url     : https://prove2.me/theorems/e5fcf217-d5f4-49dc-ab72-677a4f384969
-- title:
--   Local Inv: matches chi
-- statement:
--   The Local Inv construction uses the matches chi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/WeightRegularOfExt.lean#L277-L282
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/WeightRegularOfExt.lean#L277-L282

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataN
import Definitions.Def_Formalism_LocalRingCardinality_DataRows
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ThetaLiftGeometry_NoLocalInvariants
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ThetaLiftGeometry_TemperedRepresentations
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_WeightRegularOfExt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.LocalInv
open NumberField IsDedekindDomain Polynomial Matrix Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.IndefiniteRowSideFullHecke.NoLocalInvariantsRankParts
variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)

theorem GlobalTheory.LocalInv.matches_chi (i : N.Loc) (j : ℕ) :
    Matches N A i (charRep N i (N.chi i 1 * eps N i ^ j)) (A.tw (A.muC i) A.etaTinv)
      (((R.t : ℝ) - 1) / 2 + (1 - (R.nV : ℝ)) / 2 + j) := by sorry
