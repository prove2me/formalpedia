-- Prove2me | Theorems.Thm_GlobalTheory_UU_phi_comm
-- name    : GlobalTheory.UU.phi_comm
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T16:00:27.944219+00:00
-- url     : https://prove2.me/theorems/0ccf6f63-fd7e-44d3-8c3e-f060bee65aa2
-- title:
--   UU: phi comm
-- statement:
--   The UU construction uses the phi comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ChainVal.lean#L101-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ChainVal.lean#L101-L125

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueSamePt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ChainVal
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
open GlobalTheory.UU
open ReciprocityTheory.ChartRestriction.G.DVR
noncomputable section
open GlobalTheory GlobalTheory.UU
variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]

theorem GlobalTheory.UU.phi_comm : (GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (N : ℕ) (g : GtPtF D F), GtTors D N g → ∀ (α mu : D.X) (w : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F g.b) (DegPre.lineε N))) (u : LB.Gen (LB.LinComb D.P.L (DegPre.deltaφ D F N α mu) (DegPre.deltaε N))) (p : LB.Gen (LB.LinComb D.P.L (DegPre.phiφ D F 0 α g.b) (DegPre.deltaε N))) (p' : LB.Gen (LB.LinComb D.P.L (DegPre.phiφ D F 0 (α + N • mu) g.b) (DegPre.deltaε N))), w.IsGen → u.IsGen → p.IsGen → p'.IsGen → LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ p (DegPre.zF D F).left) (LB.mulGen D.P.L _ _ _ _ (g.s α) w) → LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ p' (DegPre.zF D F).left) (LB.mulGen D.P.L _ _ _ _ (g.s (α + N • mu)) w) → ∀ z J, Good D.P.L z J → val p' (𝟙 _) z J * val u (DegPre.trPt D F g.b).left z J = val u (𝟙 _) z J * val p (DegPre.trF D F mu).left z J) := by sorry
