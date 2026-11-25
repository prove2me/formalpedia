-- Prove2me | Theorems.Thm_GlobalTheory_IntegralFrameAllCompare_intAll_iff
-- name    : GlobalTheory.IntegralFrameAllCompare.intAll_iff
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:11:46.613818+00:00
-- url     : https://prove2.me/theorems/aba8f948-040c-40b6-b22b-d8aefd47bd42
-- title:
--   Integral Frame All Compare: int All iff
-- statement:
--   The Integral Frame All Compare construction uses the int All iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/VVNonnegIffLeOne.lean#L179-L181
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/VVNonnegIffLeOne.lean#L179-L181

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IntAllFree
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_IntegralFrameAcquisition
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingIntegralClosure
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_VVNonnegIffLeOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open GlobalTheory GlobalTheory.IntegralFrameAllCompare
open NumberField IsDedekindDomain IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.IndefiniteRowSideFullHecke.IntegralFrameAcquisition
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} (Xo : Moduli Dw l) (c : Coeff l)

theorem GlobalTheory.IntegralFrameAllCompare.intAll_iff : Formalism.L2.PjFree.IntAll Xo c ↔ AllAcquireIntegralFrame Xo c := by sorry
