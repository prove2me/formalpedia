-- Prove2me | Theorems.Thm_GlobalTheory_ConvexCutOff_polyDeriv_rename_of_convex
-- name    : GlobalTheory.ConvexCutOff.polyDeriv_rename_of_convex
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:02:48.032973+00:00
-- url     : https://prove2.me/theorems/6ee53923-0ef3-436a-b07f-ca154b0475e0
-- title:
--   Convex Cut Off: poly Deriv rename of convex
-- statement:
--   The Convex Cut Off construction uses the poly Deriv rename of convex property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/PolyDerivRenameOfConvex.lean#L156-L169
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/PolyDerivRenameOfConvex.lean#L156-L169

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsPermOfOfFnPerm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_PolyDerivRenameOfConvex
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open GlobalTheory GlobalTheory.ConvexCutOff

theorem GlobalTheory.ConvexCutOff.polyDeriv_rename_of_convex : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] (K : Set V) (F : V → ℂ), Convex ℝ K → (∀ z, z ∉ K → F z = 0) → DifferentiableOn ℂ F (interior K) → ∀ (x : V) (ι κ : Type) (ρ : ι → κ), Function.Injective ρ → ∀ (Q : MvPolynomial ι ℂ) (u : κ → V), polyDeriv (MvPolynomial.rename ρ Q) u F x = polyDeriv Q (u ∘ ρ) F x := by sorry
