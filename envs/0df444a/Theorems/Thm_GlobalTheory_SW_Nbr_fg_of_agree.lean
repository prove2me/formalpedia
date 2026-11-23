-- Prove2me | Theorems.Thm_GlobalTheory_SW_Nbr_fg_of_agree
-- name    : GlobalTheory.SW.Nbr.fg_of_agree
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:56:46.862915+00:00
-- url     : https://prove2.me/theorems/04d9b785-987f-4298-9043-6492eb1b0775
-- title:
--   Nbr: fg of agree
-- statement:
--   The Nbr construction uses the fg of agree property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/NeBotOfNorm.lean#L144-L150
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/NeBotOfNorm.lean#L144-L150

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_CycOfPrime
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_NeBotOfNorm
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
open scoped ComplexConjugate ComplexOrder Real Classical nonZeroDivisors
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.Nbr
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}
omit [IsCMField E]

theorem GlobalTheory.SW.Nbr.fg_of_agree {m : ℕ} {Λ Λ' : Lt E n} (h : Λ.FG) (ha : Agree m Λ Λ') : Λ'.FG := by sorry
