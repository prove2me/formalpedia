-- Prove2me | Theorems.Thm_GlobalTheory_Ex_RecPeriods_uth_iso
-- name    : GlobalTheory.Ex.RecPeriods.uth_iso
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T09:16:15.634319+00:00
-- url     : https://prove2.me/theorems/8cedacc2-07c5-4dd1-9a69-a4719856fe77
-- title:
--   Rec Periods: uth iso
-- statement:
--   The Rec Periods construction uses the uth iso property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsIsoOnG.lean#L73-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsIsoOnG.lean#L73-L92

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

theorem GlobalTheory.Ex.RecPeriods.uth_iso (m : ℕ) (hm : Odd m) (b x : B.A) (hb : b ^ m ^ 2 = 1) :
    B'.uth m (I.φ b) (I.φ x) = (I.lam * I.h x ^ m ^ 2 : Oˣ) * B.uth m b x := by sorry
