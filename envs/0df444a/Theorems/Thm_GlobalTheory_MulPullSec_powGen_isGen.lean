-- Prove2me | Theorems.Thm_GlobalTheory_MulPullSec_powGen_isGen
-- name    : GlobalTheory.MulPullSec.powGen_isGen
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T18:27:56.4801+00:00
-- url     : https://prove2.me/theorems/11f860fa-dc57-40d0-81df-96fb6f13ec22
-- title:
--   Mul Pull Sec: pow Gen is Gen
-- statement:
--   The Mul Pull Sec construction uses the pow Gen is Gen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaFamilyOrigin/ExistsMulPullSec.lean#L35-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaFamilyOrigin/ExistsMulPullSec.lean#L35-L43

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_ExistsMulPullSec
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.MulPullSec
variable {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K]

theorem GlobalTheory.MulPullSec.powGen_isGen {φ : K → (Y ⟶ X)} {ε : K → ℤ} {t : LB.Gen (LB.LinComb L φ ε)} (ht : t.IsGen) (N : ℕ) :
    (powGen t N).IsGen := by sorry
