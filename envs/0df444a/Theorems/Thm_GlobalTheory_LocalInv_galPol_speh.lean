-- Prove2me | Theorems.Thm_GlobalTheory_LocalInv_galPol_speh
-- name    : GlobalTheory.LocalInv.galPol_speh
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T19:24:36.278799+00:00
-- url     : https://prove2.me/theorems/5fb0a07e-819c-454f-a6cc-e7806f47fdcc
-- title:
--   Local Inv: gal Pol speh
-- statement:
--   The Local Inv construction uses the gal Pol speh property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/WeightRegularOfExt.lean#L258-L265
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/WeightRegularOfExt.lean#L258-L265

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

theorem GlobalTheory.LocalInv.galPol_speh (p : Part A.CG) (w : PlE H) (ha : A.unr (A.locG p.π w)) (s : ℝ) :
    A.unr (spehLoc N A p w) ∧ galPol A (A.lpTw (spehLoc N A p w) s) =
      ∏ k ∈ Finset.range p.d, galPol A (A.lpTw (A.locG p.π w) (((p.d : ℝ) - 1) / 2 - k + s)) := by sorry
