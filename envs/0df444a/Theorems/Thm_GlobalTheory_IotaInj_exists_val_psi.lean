-- Prove2me | Theorems.Thm_GlobalTheory_IotaInj_exists_val_psi
-- name    : GlobalTheory.IotaInj.exists_val_psi
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T14:02:52.116004+00:00
-- url     : https://prove2.me/theorems/2b56736d-ebf1-5730-9bc6-6689f6a87703
-- title:
--   Iota Inj: exists val psi
-- statement:
--   The Iota Inj construction uses the exists val psi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/MemOfNonempty.lean#L65-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/MemOfNonempty.lean#L65-L81

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IsNsmulIffEq
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_GenCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ExistsZeroGt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DataRigidSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DvrLem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThetaVV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_TXFrame
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_MemOfNonempty
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
open GlobalTheory GlobalTheory.IotaInj
open GlobalTheory.TorusExt
variable {R : Type} [CommRing R] [IsDomain R] {F : Type} [Field F] [Algebra (FractionRing R) F]

theorem GlobalTheory.IotaInj.exists_val_psi (D : DegPre R) {I : Ideal R} {χ : D.X} (hχ : D.PsiIn χ I) (hc : (D.c χ).left = eSec D.P.A)
    (j : D.P.L.ι) {V : (Spec (CommRingCat.of R)).Opens} (hV : IsAffineOpen V) (hle : V ≤ eSec D.P.A ⁻¹ᵁ D.P.L.U j)
    (y : Spec (CommRingCat.of F)) (hy : (jFK (R := R) F ≫ jK R) y ∈ V)
    (J : (Spec (CommRingCat.of F) ⟶ D.P.A.left) → D.P.L.ι) (hj : J ((jFK (R := R) F ≫ jK R) ≫ eSec D.P.A) = j) :
    ∃ r ∈ I.map (DegPre.toOpen V), (val (D.psi χ) (jFK (R := R) F) y J).val = gs (jFK (R := R) F ≫ jK R) y V r := by sorry
