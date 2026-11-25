-- Prove2me | Theorems.Thm_GlobalTheory_SW_TwistAdm_gidx_pos
-- name    : GlobalTheory.SW.TwistAdm.gidx_pos
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:21:54.285744+00:00
-- url     : https://prove2.me/theorems/fe5507da-4355-4bd2-815f-967c1f9de9e5
-- title:
--   Twist Adm: gidx pos
-- statement:
--   The Twist Adm construction uses the gidx pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/TwistAdmissible.lean#L383-L386
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/TwistAdmissible.lean#L383-L386

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_TwistAdmissible
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.TwistAdm
variable {E : Type} [Field E] [NumberField E] {n N : ℕ}
variable [IsCMField E]
omit [IsCMField E]

theorem GlobalTheory.SW.TwistAdm.gidx_pos {m : ℕ} {𝔛 : Lt E N} (hfg : 𝔛.FG) (hA : Agree m 𝔛 (stdL E N)) : 0 < gidx 𝔛 := by sorry
