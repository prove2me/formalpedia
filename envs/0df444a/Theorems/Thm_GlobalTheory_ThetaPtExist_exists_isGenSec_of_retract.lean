-- Prove2me | Theorems.Thm_GlobalTheory_ThetaPtExist_exists_isGenSec_of_retract
-- name    : GlobalTheory.ThetaPtExist.exists_isGenSec_of_retract
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T21:07:43.875793+00:00
-- url     : https://prove2.me/theorems/25fcf0b2-a73e-421c-aa16-b598c8e89216
-- title:
--   Theta Pt Exist: exists is Gen Sec of retract
-- statement:
--   The Theta Pt Exist construction uses the exists is Gen Sec of retract property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Statements/TorsionEndomorphisms/ExistsGeneratorOfIsField.lean#L82-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Statements/TorsionEndomorphisms/ExistsGeneratorOfIsField.lean#L82-L98

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SectionArithmetic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueSecEqMulGen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ThetaGrpActsLinearly
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_WeilIsIffCommIsOfAndLiftSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Statements_TorsionEndomorphisms_ExistsGeneratorOfIsField
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
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.ThetaPtExist
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {T : Over S}
open ThetaAct

theorem GlobalTheory.ThetaPtExist.exists_isGenSec_of_retract (hL : L.IsLB) {a : ℤ} {T' : Over S} (i : T' ⟶ T) (h : T ⟶ T')
    (hi : i ≫ h = 𝟙 T') (t : SecM A L a T) (ht : ∀ s, ∃ r : Γ(T.left, ⊤), r • t = s) :
    ∃ th, IsGenSec A L a (T := T') th := by sorry
