-- Prove2me | Theorems.Thm_GlobalTheory_Ex_RecPeriods_dbl_iso
-- name    : GlobalTheory.Ex.RecPeriods.dbl_iso
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:57:32.154936+00:00
-- url     : https://prove2.me/theorems/76f9bf71-e458-4499-9670-6cb0409adb5d
-- title:
--   Rec Periods: dbl iso
-- statement:
--   The Rec Periods construction uses the dbl iso property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsIsoOnG.lean#L30-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsIsoOnG.lean#L30-L38

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_NotAllMatchRankZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_MulqLawsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_DegenerationDataTorsionStructureAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsIsoOnG
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators
noncomputable section
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.RecPeriods
variable {O : Type} [CommRing O] {B B' : NumB O} (I : NumB.Iso B B')

theorem GlobalTheory.Ex.RecPeriods.dbl_iso (x : B.A) : dbl B'.θ B'.σ (I.φ x) * I.h (x * x) = dbl B.θ B.σ x * I.h x ^ 4 := by sorry
