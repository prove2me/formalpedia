-- Prove2me | Theorems.Thm_GlobalTheory_SplitTorus_bcIso_hom_fst
-- name    : GlobalTheory.SplitTorus.bcIso_hom_fst
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:35:38.649101+00:00
-- url     : https://prove2.me/theorems/aa8700fa-2656-4396-b1ef-f26c62e6a7ba
-- title:
--   Split Torus: bc Iso hom fst
-- statement:
--   The Split Torus construction uses the bc Iso hom fst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/HomBaseChangeBijectiveOfLeNilradical.lean#L636-L638
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/HomBaseChangeBijectiveOfLeNilradical.lean#L636-L638

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_Torus2GammaBijective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_AbelianSchemeQuotients_QSurjective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HomBaseChangeBijectiveOfLeNilradical
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
universe u
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht
open AddMonoidAlgebra (single)
open GlobalTheory
open GlobalTheory.SplitTorus
variable {S S' : Scheme.{u}} (f : S' ⟶ S) (X Y : Type u) [AddCommGroup X] [AddCommGroup Y]

theorem GlobalTheory.SplitTorus.bcIso_hom_fst :
    (bcIso f X).hom.left ≫ pullback.fst (splitTorus S X).hom f = bcMap f X := by sorry
