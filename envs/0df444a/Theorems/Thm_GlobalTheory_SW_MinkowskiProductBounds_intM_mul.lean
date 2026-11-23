-- Prove2me | Theorems.Thm_GlobalTheory_SW_MinkowskiProductBounds_intM_mul
-- name    : GlobalTheory.SW.MinkowskiProductBounds.intM_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:52:59.568796+00:00
-- url     : https://prove2.me/theorems/c8499a37-dc9a-449a-8dec-23a1684caa30
-- title:
--   Minkowski Product Bounds: int M mul
-- statement:
--   The Minkowski Product Bounds construction uses the int M mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ExistsShortIso.lean#L305-L308
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ExistsShortIso.lean#L305-L308

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
omit [NumberField E] [IsCMField E]

theorem GlobalTheory.SW.MinkowskiProductBounds.intM_mul {α β γ : Type} [Fintype β] {A : Matrix α β E} {B : Matrix β γ E} (hA : IntM A)
    (hB : IntM B) : IntM (A * B) := by sorry
