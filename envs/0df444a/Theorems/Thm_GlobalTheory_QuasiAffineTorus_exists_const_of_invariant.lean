-- Prove2me | Theorems.Thm_GlobalTheory_QuasiAffineTorus_exists_const_of_invariant
-- name    : GlobalTheory.QuasiAffineTorus.exists_const_of_invariant
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T14:44:28.656638+00:00
-- url     : https://prove2.me/theorems/6e3d8455-0b10-4f03-b56f-5761abe86eb7
-- title:
--   Quasi Affine Torus: exists const of invariant
-- statement:
--   The Quasi Affine Torus construction uses the exists const of invariant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/QuasiAffineSubgroupContainingTorusEqTorus.lean#L262-L359
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/QuasiAffineSubgroupContainingTorusEqTorus.lean#L262-L359

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsIsClosedImageOfIsClosedSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_GeometricallyReducedOfPerfectField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_InvariantFunctionsDescend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsAffineOpenAndBijectiveOfWeightUnits
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsIntegralOfSmoothFieldOfConnectedSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsReducedAlgebraOfSmoothOfIsNoetherianRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_GeometricallyConnectedOfIsPullbackOfSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_QuasiAffineSubgroupContainingTorusEqTorus
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
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
open GlobalTheory GlobalTheory.QuasiAffineTorus
open RationalPoint
variable {k : Type} [Field k]
variable [IsAlgClosed k]

theorem GlobalTheory.QuasiAffineTorus.exists_const_of_invariant {G B T N : Over (Sp k)} [GrpObj G] [GrpObj B] [GrpObj T]
    [GrpObj N] (i : T ⟶ G) (q : G ⟶ B) (ν : N ⟶ G) (i' : T ⟶ N) [IsMonHom q] [IsMonHom ν]
    [Smooth q.left] [Surjective q.left] [QuasiCompact q.left] [IsProper B.hom] [Smooth T.hom]
    [Smooth N.hom] [QuasiCompact N.hom] [IsIntegral N.left] [IsClosedImmersion ν.left]
    (hk : IsPullback i (toUnit _) q η[B]) (hi : i' ≫ ν = i) (f : Γ(N.left, ⊤))
    (hf : ∀ (t : 𝟙_ (Over (Sp k)) ⟶ T) (y : 𝟙_ (Over (Sp k)) ⟶ N),
      ev ((t ≫ i') * y) f = ev y f) : ∃ r, const N r = f := by sorry
