-- Prove2me | Theorems.Thm_GlobalTheory_SplitTorus_comm_bcMap_iff
-- name    : GlobalTheory.SplitTorus.comm_bcMap_iff
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T20:21:37.774185+00:00
-- url     : https://prove2.me/theorems/6196fa3c-7236-450e-839d-16742bb33762
-- title:
--   Split Torus: comm bc Map iff
-- statement:
--   The Split Torus construction uses the comm bc Map iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/HomBaseChangeBijectiveOfLeNilradical.lean#L699-L713
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/HomBaseChangeBijectiveOfLeNilradical.lean#L699-L713

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
variable {X Y}

theorem GlobalTheory.SplitTorus.comm_bcMap_iff (g : splitTorus S X ⟶ splitTorus S Y)
    (g' : splitTorus S' X ⟶ splitTorus S' Y) :
    g'.left ≫ bcMap f Y = bcMap f X ≫ g.left ↔
      g' ≫ (bcIso f Y).hom = (bcIso f X).hom ≫ (Over.pullback f).map g := by sorry
