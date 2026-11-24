-- Prove2me | Theorems.Thm_GlobalTheory_IsoLift_cls_eq_iff_modN
-- name    : GlobalTheory.IsoLift.cls_eq_iff_modN
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T18:43:03.396258+00:00
-- url     : https://prove2.me/theorems/19e85c5d-d380-449f-87ab-f66d38296973
-- title:
--   Iso Lift: cls eq iff mod N
-- statement:
--   The Iso Lift construction uses the cls eq iff mod N property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsIsometryLift.lean#L76-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsIsometryLift.lean#L76-L78

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_LevelActionTransitions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ModNOfDvdModulus
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsIsometryLift
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory GlobalTheory.IsoLift
open GlobalTheory.SimLift GlobalTheory.IndefiniteRowSideFullHecke.LevelActionTransitions
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H)

theorem GlobalTheory.IsoLift.cls_eq_iff_modN {n : ℕ+} {a b : D.La} : cls D n a = cls D n b ↔ D.ModN n (a - b) := by sorry
