-- Prove2me | Theorems.Thm_GlobalTheory_SW_MinkowskiProductBounds_li_of_mul
-- name    : GlobalTheory.SW.MinkowskiProductBounds.li_of_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:47:33.077083+00:00
-- url     : https://prove2.me/theorems/a801504c-acdf-48b5-af43-a9fe0a7c742a
-- title:
--   Minkowski Product Bounds: li of mul
-- statement:
--   The Minkowski Product Bounds construction uses the li of mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ExistsShortIso.lean#L314-L316
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ExistsShortIso.lean#L314-L316

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

theorem GlobalTheory.SW.MinkowskiProductBounds.li_of_mul {k a b : ℕ} {A : Matrix (Fin k) (Fin a) E} {R : Matrix (Fin a) (Fin b) E}
    (h : LinearIndependent E fun i => (A * R) i) : LinearIndependent E fun i => A i := by sorry
