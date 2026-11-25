-- Prove2me | Theorems.Thm_GlobalTheory_SW_MinkowskiProductBounds_ccT_smul
-- name    : GlobalTheory.SW.MinkowskiProductBounds.ccT_smul
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T19:43:37.296266+00:00
-- url     : https://prove2.me/theorems/52b30276-d6bb-476e-a2a9-35c4a7ebff09
-- title:
--   Minkowski Product Bounds: cc T smul
-- statement:
--   The Minkowski Product Bounds construction uses the cc T smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ExistsShortIso.lean#L295-L298
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ExistsShortIso.lean#L295-L298

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsNeZeroNormSqLeMulCovolumeRpow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsShortIso
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
open scoped ComplexConjugate ComplexOrder Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.MinkowskiProductBounds
open Module Submodule
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Finset (E →+* ℂ)}

theorem GlobalTheory.SW.MinkowskiProductBounds.ccT_smul {α β : Type} (k : ℤ) (A : Matrix α β E) :
    ccT ((k : E) • A) = (k : E) • ccT A := by sorry
