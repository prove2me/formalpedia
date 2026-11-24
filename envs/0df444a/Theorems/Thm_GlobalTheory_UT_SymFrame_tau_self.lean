-- Prove2me | Theorems.Thm_GlobalTheory_UT_SymFrame_tau_self
-- name    : GlobalTheory.UT.SymFrame.tau_self
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T21:19:55.908343+00:00
-- url     : https://prove2.me/theorems/681c73af-da47-4cf1-992d-b57cfb9754a0
-- title:
--   Sym Frame: tau self
-- statement:
--   The Sym Frame construction uses the tau self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/UnivIdentity.lean#L245-L280
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/UnivIdentity.lean#L245-L280

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ExistsZeroGt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DataRigidSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DvrLem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThetaVV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_TXFrame
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_UnivIdentity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT
noncomputable section
open GlobalTheory GlobalTheory.UT GlobalTheory.UT.SymFrame
variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {Y : Over (Spec (CommRingCat.of R))}
variable {F : Type} [Field F] [Algebra (FractionRing R) F]

theorem GlobalTheory.UT.SymFrame.tau_self (hE : D.PsiEven) (hB : D.TauBimult) (y : D.X) {z : (TF (R := R) F).left} {J} (hJ : Good D.P.L z J) :
    val (D.tau y y) ((𝟙 (TF (R := R) F) :).left ≫ jFK (R := R) F) z J =
      cubV D.cub z J (cP D (TF (R := R) F) y) (cP D _ y)⁻¹ (cP D _ y) * (val D.sym (cP D (TF (R := R) F) y).left z J)⁻¹ *
        (@id ((TF (R := R) F).left.presheaf.stalk z)ˣ (val (D.psi y) (jFK (R := R) F) z J) *
          rigV D (TF (R := R) F).hom z J) ^ 2 := by sorry
