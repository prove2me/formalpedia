-- Prove2me | Theorems.Thm_GlobalTheory_ClosedFibreTerm_vanish_of_terms_vanish
-- name    : GlobalTheory.ClosedFibreTerm.vanish_of_terms_vanish
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T11:28:15.964857+00:00
-- url     : https://prove2.me/theorems/3b4b68c1-fc2a-4703-98d5-de3d973247e4
-- title:
--   Closed Fibre Term: vanish of terms vanish
-- statement:
--   The Closed Fibre Term construction uses the vanish of terms vanish property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/RingsOfIntegers/VanishOfTermsVanish.lean#L17-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/RingsOfIntegers/VanishOfTermsVanish.lean#L17-L33

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ValuationMultiplicationInvariance
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBCPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ProdExpPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_WeightedChartPullback_WeightIndep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_PGAppEqZeroIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_VanishOfTermsVanish
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.ClosedFibreTerm
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem GlobalTheory.ClosedFibreTerm.vanish_of_terms_vanish {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
    {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
    {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (e k : ℕ)
    (σ : H0 U.LG.L k) (f : ∀ α : D.toPre.X, D.toPre.SecB k α) (h : U.ExpandsAt e k σ f)
    (h0 : ∀ α j, ((U.gt e).pG.left.app _).hom ((f α).f j) = 0) (j) :
    ((fstG I e G).left.app _).hom (σ.f j) = 0 := by sorry
