-- Prove2me | Theorems.Thm_GlobalTheory_LocalInv_part_alg
-- name    : GlobalTheory.LocalInv.part_alg
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T19:24:55.47197+00:00
-- url     : https://prove2.me/theorems/55b8f50f-7726-4d53-b058-2746945ca229
-- title:
--   Local Inv: part alg
-- statement:
--   The Local Inv construction uses the part alg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/WeightRegularOfExt.lean#L326-L353
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/WeightRegularOfExt.lean#L326-L353

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

theorem GlobalTheory.LocalInv.part_alg (hη : EtaType N A) (hW : WeightRegular N A) (i : N.Loc) (P : A.AV i)
    (Pa : List (Part A.CG)) (hB : IsBCV N A i P Pa) (p : Part A.CG) (hp : p ∈ Pa) (ha : Odd p.a)
    (hd : Odd p.d) : A.csd (A.tw p.π A.etaT) ∧ A.ralg (A.tw p.π A.etaT) := by sorry
