-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HopfSys_primitive_structure_sheaf_cohomology_class
-- name    : GlobalTheory.CompanionTheory.HopfSys.primitive_structure_sheaf_cohomology_class
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T00:37:06.186331+00:00
-- url     : https://prove2.me/theorems/a59cc086-fa7a-404e-b139-1dbdfe237f9b
-- title:
--   Hopf Sys: primitive structure sheaf cohomology class
-- statement:
--   The Hopf Sys construction uses the primitive structure sheaf cohomology class property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CechTripleRestrictCompositeInjectiveCohomologyFo.lean#L184-L216
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CechTripleRestrictCompositeInjectiveCohomologyFo.lean#L184-L216

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CechTripleRestrictCompositeInjectiveSecond
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CechTripleRestrictCompositeInjectiveCohomologyFo
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
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge Limits
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HopfSys
variable {R : Type} [CommRing R]
variable (A : Over (Sp R)) [GrpObj A]

theorem GlobalTheory.CompanionTheory.HopfSys.primitive_structure_sheaf_cohomology_class
    (hAx : ∀ c : HO1 (A ⊗ A).hom, IsPullO (wOver (lift (𝟙 A) (1 : A ⟶ A))) c 0 →
      IsPullO (wOver (lift (1 : A ⟶ A) (𝟙 A))) c 0 → c = 0) (c : HO1 A.hom) :
    pullHO1 (wOver μ[A]) c = pullHO1 (wOver (fst A A)) c + pullHO1 (wOver (snd A A)) c := by sorry
