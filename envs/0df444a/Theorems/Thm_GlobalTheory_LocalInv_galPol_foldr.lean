-- Prove2me | Theorems.Thm_GlobalTheory_LocalInv_galPol_foldr
-- name    : GlobalTheory.LocalInv.galPol_foldr
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T19:23:45.896354+00:00
-- url     : https://prove2.me/theorems/6ffdc6cb-db9a-4f4e-b5cc-94c994d4f10c
-- title:
--   Local Inv: gal Pol foldr
-- statement:
--   The Local Inv construction uses the gal Pol foldr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/WeightRegularOfExt.lean#L241-L250
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/WeightRegularOfExt.lean#L241-L250

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

theorem GlobalTheory.LocalInv.galPol_foldr {w : PlE H} (a : A.LP w) (ha : A.unr a) (e : ℝ → ℝ) (s : ℝ) (L : List ℝ) :
    A.unr (L.foldr (fun k acc => A.lpSum (A.lpTw a (e k)) acc) (A.lpZero w)) ∧
    galPol A (A.lpTw (L.foldr (fun k acc => A.lpSum (A.lpTw a (e k)) acc) (A.lpZero w)) s) =
      (L.map fun k => galPol A (A.lpTw a (e k + s))).prod := by sorry
