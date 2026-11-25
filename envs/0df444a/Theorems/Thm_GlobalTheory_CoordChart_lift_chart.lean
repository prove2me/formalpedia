-- Prove2me | Theorems.Thm_GlobalTheory_CoordChart_lift_chart
-- name    : GlobalTheory.CoordChart.lift_chart
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T15:02:03.622494+00:00
-- url     : https://prove2.me/theorems/15c6a84a-6ad4-4511-8067-feccb1099530
-- title:
--   Coord Chart: lift chart
-- statement:
--   The Coord Chart construction uses the lift chart property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ResidueGeneric.lean#L27-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ResidueGeneric.lean#L27-L69

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SecCoordBcScaleUnique
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ResidueGeneric
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory GlobalTheory.CoordChart

theorem GlobalTheory.CoordChart.lift_chart {o : Type} [CommRing o] {g n N' : ℕ} {I : Ideal (MvPolynomial (Ix g (N' ^ 2)) o)}
    (Y : MMPre n N' I) {R : Type} [CommRing R] (β : o →+* R) (x : Sp R ⟶ Y.MM) (v : Ix g (N' ^ 2) → R)
    {K : Type} [Field K] (y : R →+* K) [IsOpenImmersion x] (hx : x ≫ Y.s = spMap β)
    (hv : SecCoord Y.de Y.th x v) (c : Kˣ)
    {L : Type} [CommRing L] (ψ : L →+* K) (hψ : ∀ l, ψ l ≠ 0 → IsUnit l) (β' : o →+* L)
    (w : Ix g (N' ^ 2) → L) (hβ : ψ.comp β' = y.comp β) (hw : ∀ a, ψ (w a) = c * y (v a))
    (hI : ∀ F ∈ I, MvPolynomial.eval₂ β' w F = 0) :
    ∃ φ : R →+* L, ψ.comp φ = y ∧ φ.comp β = β' ∧ ∃ u : Lˣ, ∀ a, w a = u * φ (v a) := by sorry
