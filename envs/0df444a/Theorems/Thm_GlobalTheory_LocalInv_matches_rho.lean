-- Prove2me | Theorems.Thm_GlobalTheory_LocalInv_matches_rho
-- name    : GlobalTheory.LocalInv.matches_rho
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T19:23:02.146384+00:00
-- url     : https://prove2.me/theorems/8c00089d-c7cc-43a7-9fe8-9f40ea8a7eb8
-- title:
--   Local Inv: matches rho
-- statement:
--   The Local Inv construction uses the matches rho property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/WeightRegularOfExt.lean#L284-L324
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/WeightRegularOfExt.lean#L284-L324

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

theorem GlobalTheory.LocalInv.matches_rho (i : N.Loc) (x : N.X i) (π : A.CG R.r) (P : A.AV i) (hP : A.ptV i P = some x)
    (hB : IsBCV N A i P (twistIso N A ([⟨R.r, π, 1⟩] ++ [muPart N A i]) A.etaTinv))
    (ρ : G H.E N.Om →* GL (Fin R.r) (N.O i)) (hρ : IsRankPart N i x ρ) :
    Matches N A i ρ (A.tw π A.etaTinv) ((1 - (R.nV : ℝ)) / 2) := by sorry
