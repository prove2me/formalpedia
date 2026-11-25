-- Prove2me | Theorems.Thm_GlobalTheory_Diag_exists_isPullback
-- name    : GlobalTheory.Diag.exists_isPullback
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T14:07:49.034889+00:00
-- url     : https://prove2.me/theorems/7f875e6e-9e5a-4881-bf06-00dbd7a26a83
-- title:
--   Diag: exists is Pullback
-- statement:
--   The Diag construction uses the exists is Pullback property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/LocallyOfFinitePresentationDiagMap.lean#L342-L350
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/LocallyOfFinitePresentationDiagMap.lean#L342-L350

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_AbelianSchemeQuotients_IsAbelianScheme
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_Torus2GammaBijective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_DimSplitPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_LinCombTrivG
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FinitePresentationOfInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentationDiagMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht
open GlobalTheory GlobalTheory.Diag
variable (S : Scheme.{u}) {X Y Z : Type u} [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
variable (R : Type u) [CommRing R] (X : Type u) [AddCommGroup X]
attribute [local instance] intAlgebra
open scoped AlgebraMonoidAlgebra
variable {S R}

theorem GlobalTheory.Diag.exists_isPullback (g : S ⟶ Spec (.of R)) :
    ∃ a : (splitTorus S X).left ⟶ Spec (.of (AddMonoidAlgebra R X)),
      IsPullback a (splitTorus S X).hom
        (Spec.map (CommRingCat.ofHom (algebraMap R (AddMonoidAlgebra R X)))) g := by sorry
