-- Prove2me | Theorems.Thm_GlobalTheory_ZH_ConePrime_exists_point
-- name    : GlobalTheory.ZH.ConePrime.exists_point
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T22:01:35.470864+00:00
-- url     : https://prove2.me/theorems/32706ebe-0c40-4324-a797-ec33e18ffec2
-- title:
--   Cone Prime: exists point
-- statement:
--   The Cone Prime construction uses the exists point property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/VanishingIdealConePrimeHomogeneous.lean#L166-L175
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/VanishingIdealConePrimeHomogeneous.lean#L166-L175

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PullChartIsLB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsUnitCharts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_RingKrullDimOfEtaleMvPolynomial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TangentBijectionOfValues
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_VanishingIdealConePrimeHomogeneous
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
noncomputable section
open GlobalTheory GlobalTheory.ZH GlobalTheory.ZH.ConePrime
open GlobalTheory.ZH.CrdCalc GlobalTheory.TangentOrigin
variable {k : Type} [Field k] {X : Scheme.{0}}

theorem GlobalTheory.ZH.ConePrime.exists_point (p : X ⟶ Sp k) {U : X.Opens} (hU : IsAffineOpen U) (e : Γ(X, U) →+* k)
    (he : ∀ a, e (constHom p U a) = a) :
    ∃ (x : Sp k ⟶ X) (h : ⊤ ≤ x ⁻¹ᵁ U), x ≫ p = 𝟙 _ ∧ valHom x U h = e := by sorry
