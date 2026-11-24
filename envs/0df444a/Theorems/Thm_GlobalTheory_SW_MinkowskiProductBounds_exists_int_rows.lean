-- Prove2me | Theorems.Thm_GlobalTheory_SW_MinkowskiProductBounds_exists_int_rows
-- name    : GlobalTheory.SW.MinkowskiProductBounds.exists_int_rows
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T19:42:42.659108+00:00
-- url     : https://prove2.me/theorems/8fc0099a-7435-41ae-bd62-2f06adc77674
-- title:
--   Minkowski Product Bounds: exists int rows
-- statement:
--   The Minkowski Product Bounds construction uses the exists int rows property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ExistsShortIso.lean#L344-L369
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ExistsShortIso.lean#L344-L369

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

theorem GlobalTheory.SW.MinkowskiProductBounds.exists_int_rows {N m n D : ℕ} (hD : 0 < D) {G : Matrix (Fin m) (Fin m) E} (h0 : G.det ≠ 0)
    {W : Matrix (Fin N) (Fin m) E} (hW : IsoRows G W) {V : Matrix (Fin n) (Fin m) E}
    {S : Matrix (Fin m) (Fin n) E} (hS : S * V = 1) :
    ∃ T : Matrix (Fin N) (Fin n) E, IntM T ∧ IsoRows' (V * ((D : E) • G) * ccT V) T := by sorry
