-- Prove2me | Theorems.Thm_GlobalTheory_SW_MinkowskiProductBounds_det_le
-- name    : GlobalTheory.SW.MinkowskiProductBounds.det_le
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T19:42:54.267835+00:00
-- url     : https://prove2.me/theorems/f16a02c0-7470-4962-a365-c0024ca98c51
-- title:
--   Minkowski Product Bounds: det le
-- statement:
--   The Minkowski Product Bounds construction uses the det le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ExistsShortIso.lean#L318-L339
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ExistsShortIso.lean#L318-L339

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

theorem GlobalTheory.SW.MinkowskiProductBounds.det_le (h : IsType Ψ) {m D : ℕ} (hD : 0 < D) {G : Matrix (Fin m) (Fin m) E}
    {H : CM Ψ m m} (h0 : G.det ≠ 0) (hG : Den D G⁻¹) (hH : IsMaj Ψ G H) :
    ∏ τ, ‖(H τ).det‖ ≤ ∏ _τ : Ψ, (D : ℝ) ^ m := by sorry
