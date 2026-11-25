-- Prove2me | Theorems.Thm_GlobalTheory_KunnethDomain_sval_scale
-- name    : GlobalTheory.KunnethDomain.sval_scale
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T15:07:34.89105+00:00
-- url     : https://prove2.me/theorems/a72b556e-8c4c-50ea-83e1-4169de19cfe5
-- title:
--   Kunneth Domain: sval scale
-- statement:
--   The Kunneth Domain construction uses the sval scale property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsSmulEqSumMulOfIsDomain.lean#L34-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsSmulEqSumMulOfIsDomain.lean#L34-L37

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SectionLinCombFiberProductSeparatedStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsSecOfGenericFibre
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_AppCompatGeneric
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsSmulEqSumMulOfIsDomain
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory
open GlobalTheory.KunnethDomain
open ReciprocityTheory.ChartRestriction.G.DVR
variable {X Y Y' T : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K] [Fintype K']

theorem GlobalTheory.KunnethDomain.sval_scale {φ : K → (Y ⟶ X)} {ε : K → ℤ} (c : Γ(Y, ⊤)) (s : LB.Sec (LB.LinComb L φ ε))
    (r : T ⟶ Y) (z : T) {J} (hJ : Good L z J) :
    sval (SecOps.secScale c s) r z J = gs r z ⊤ c * sval s r z J := by sorry
