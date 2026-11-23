-- Prove2me | Theorems.Thm_GlobalTheory_SW_MinkowskiProductBounds_basis_one
-- name    : GlobalTheory.SW.MinkowskiProductBounds.basis_one
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T15:55:44.495044+00:00
-- url     : https://prove2.me/theorems/9dfca50a-5b51-4928-9c52-02dcf6811fd0
-- title:
--   Minkowski Product Bounds: basis one
-- statement:
--   The Minkowski Product Bounds construction uses the basis one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ExistsShortIso.lean#L105-L141
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ExistsShortIso.lean#L105-L141

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

theorem GlobalTheory.SW.MinkowskiProductBounds.basis_one (h : IsType Ψ) : ∃ b : Basis (Free.ChooseBasisIndex ℤ (𝓞 E)) ℝ (Ψ → ℂ),
    ∀ x, x ∈ span ℤ (Set.range b) ↔ ∃ a : E, IsIntegral ℤ a ∧ x = fun τ => τ.1 a := by sorry
