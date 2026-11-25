-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Axis_bijective_tens
-- name    : GlobalTheory.CompanionTheory.Axis.bijective_tens
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T00:17:58.621025+00:00
-- url     : https://prove2.me/theorems/06349e5b-91a6-46b0-b92c-8f5558edf117
-- title:
--   Axis: bijective tens
-- statement:
--   The Axis construction uses the bijective tens property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ProductFirstCohomologyComparison.lean#L70-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ProductFirstCohomologyComparison.lean#L70-L107

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsUniqueIsPullForm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AbelianSchemeGerms
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_USt
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ProductFirstCohomologyComparison
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.Axis
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Axis
open CategoryTheory.Limits
variable {R : Type} [CommRing R] {X Y : Scheme.{0}} (f : X ⟶ Sp R) (g : Y ⟶ Sp R)

theorem GlobalTheory.CompanionTheory.Axis.bijective_tens (U : X.affineOpens) (V : Y.affineOpens) (W : (pullback f g).affineOpens)
    (hW : W.1 = pullback.fst f g ⁻¹ᵁ U.1 ⊓ pullback.snd f g ⁻¹ᵁ V.1) (s' : pullback f g ⟶ Sp R)
    (hU : W.1 ≤ pullback.fst f g ⁻¹ᵁ U.1) (hV : W.1 ≤ pullback.snd f g ⁻¹ᵁ V.1)
    (α : Sec f U.1 ⊗[R] Sec g V.1 →+* Sec s' W.1)
    (hα : ∀ b c, α (b ⊗ₜ c) = secPull (φ := pullback.fst f g) f s' ⟨(W, U), hU⟩ b *
      secPull (φ := pullback.snd f g) g s' ⟨(W, V), hV⟩ c) : Function.Bijective α := by sorry
