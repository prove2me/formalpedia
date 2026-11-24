-- Prove2me | Theorems.Thm_GlobalTheory_LocalInv_galPol_block
-- name    : GlobalTheory.LocalInv.galPol_block
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T19:36:09.339687+00:00
-- url     : https://prove2.me/theorems/9d19b8a0-5b78-4b41-99a9-5a1c43d7ae71
-- title:
--   Local Inv: gal Pol block
-- statement:
--   The Local Inv construction uses the gal Pol block property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/WeightRegularOfExt.lean#L267-L275
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/WeightRegularOfExt.lean#L267-L275

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

theorem GlobalTheory.LocalInv.galPol_block (i : N.Loc) {w : PlE H} (hw : SplitOut N i w) {B : ValuationSubring N.Om}
    {σ : G H.E N.Om} (hB : IsPlaceOver (F := H.E) B w) (hσ : IsFrob (F := H.E) B (normV w) σ) (u : ℝ) :
    galPol A (A.lpTw (A.locG (A.tw (A.muC i) A.etaTinv) w)
      (((R.t : ℝ) - 1) / 2 + (1 - (R.nV : ℝ)) / 2 + u)) =
      X - C (iotaO N A i ((N.chi i 1 σ : (N.O i)ˣ) : N.O i) * ((normV w : ℕ) : ℂ) ^ ((u : ℝ) : ℂ)) := by sorry
