-- Prove2me | Theorems.Thm_GlobalTheory_BXOf_sig_nat
-- name    : GlobalTheory.BXOf.sig_nat
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T16:52:36.792371+00:00
-- url     : https://prove2.me/theorems/34703b0e-c7e5-5010-bbce-7636592ebcbd
-- title:
--   BXOf: sig nat
-- statement:
--   The BXOf construction uses the sig nat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/BiextensionSecondLawCommutativityValue.lean#L49-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/BiextensionSecondLawCommutativityValue.lean#L49-L57

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemOfCompat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_Biextensions_GenericFiberCubeInclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_AlWellDefSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_BiextensionSecondLawCommutativityValue
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.BXOf
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
variable {R S : Type} [CommRing R] [IsLocalRing R] [CommRing S] [IsLocalRing S] {X Y : Scheme.{0}}

theorem GlobalTheory.BXOf.sig_nat (f : R →+* S) (r : Spec (CommRingCat.of R) ⟶ X) {U : X.Opens} (h : r (closedPoint R) ∈ U)
    (a : Γ(X, U)ˣ) :
    Units.map f.toMonoidHom (sig R (gm r (closedPoint R) U a)) =
      sig S (gm (Spec.map (CommRingCat.ofHom f) ≫ r) (closedPoint S) U a) := by sorry
