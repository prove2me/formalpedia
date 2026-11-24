-- Prove2me | Theorems.Thm_GlobalTheory_SW_MinkowskiProductBounds_short
-- name    : GlobalTheory.SW.MinkowskiProductBounds.short
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T19:42:53.378815+00:00
-- url     : https://prove2.me/theorems/45f02288-74fc-4c12-a345-2785de04ee1b
-- title:
--   Minkowski Product Bounds: short
-- statement:
--   The Minkowski Product Bounds construction uses the short property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ExistsShortIso.lean#L183-L251
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ExistsShortIso.lean#L183-L251

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

theorem GlobalTheory.SW.MinkowskiProductBounds.short (h : IsType Ψ) (m : ℕ) (Δ ε : ℝ) (hε : 0 < ε) : ∃ (n : ℕ) (C : ℝ),
    ∀ H : CM Ψ m m, (∀ τ, (H τ).PosDef) → ∏ τ, ‖(H τ).det‖ ≤ Δ →
    (∀ v : Fin m → E, v ≠ 0 → (∀ a, IsIntegral ℤ (v a)) → ε ≤ ∑ τ, hval Ψ H τ v) →
    ∃ V : Matrix (Fin n) (Fin m) E, IntM V ∧ (∃ S : Matrix (Fin m) (Fin n) E, S * V = 1) ∧
      ∀ i τ, hval Ψ H τ (V i) ≤ C := by sorry
