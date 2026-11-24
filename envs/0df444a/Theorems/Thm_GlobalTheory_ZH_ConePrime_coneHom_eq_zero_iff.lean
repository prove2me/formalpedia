-- Prove2me | Theorems.Thm_GlobalTheory_ZH_ConePrime_coneHom_eq_zero_iff
-- name    : GlobalTheory.ZH.ConePrime.coneHom_eq_zero_iff
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T22:01:39.070355+00:00
-- url     : https://prove2.me/theorems/6efe300a-f6eb-4b8a-9846-21942792521d
-- title:
--   Cone Prime: cone Hom eq zero iff
-- statement:
--   The Cone Prime construction uses the cone Hom eq zero iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/VanishingIdealConePrimeHomogeneous.lean#L203-L216
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/VanishingIdealConePrimeHomogeneous.lean#L203-L216

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
variable {H : LB X} {J : Type} {s : J → H.Sec}

theorem GlobalTheory.ZH.ConePrime.coneHom_eq_zero_iff [IsIntegral X] (p : X ⟶ Sp k) {K : Type} [Field K] (y : Sp K ⟶ X)
    (hy : ∀ U : X.Opens, (U : Set X).Nonempty → ⊤ ≤ y ⁻¹ᵁ U) {v : J → K} (hv : Crd H s y v) (i : J)
    (hi : ⊤ ≤ y ⁻¹ᵁ Out.nonzeroLocus (s i)) (r : J → Γ(X, Out.nonzeroLocus (s i)))
    (hr : ∀ j, IsRatio (s j) (s i) _ (r j)) (f : MvPolynomial J k) :
    coneHom (constHom p _) r f = 0 ↔
      coneHom ((evalPt (y ≫ p) ⊤ le_rfl).comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom) v f = 0 := by sorry
