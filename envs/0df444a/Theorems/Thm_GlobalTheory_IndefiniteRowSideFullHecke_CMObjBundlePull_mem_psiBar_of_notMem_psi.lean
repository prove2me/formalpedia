-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_CMObjBundlePull_mem_psiBar_of_notMem_psi
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.CMObjBundlePull.mem_psiBar_of_notMem_psi
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:08:53.619988+00:00
-- url     : https://prove2.me/theorems/83bbb343-2983-41ab-b5ad-e832376e47d7
-- title:
--   CMObj Bundle Pull: mem psi Bar of not Mem psi
-- statement:
--   The CMObj Bundle Pull construction uses the mem psi Bar of not Mem psi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/JetGauges/CMObjBundlePull.lean#L176-L183
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/JetGauges/CMObjBundlePull.lean#L176-L183

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IsCombAt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_RosatiAdj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ConstGen
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_StatementB
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_CMObjBundlePull
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.CMObjBundlePull
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.LamCM
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Level H}
attribute [instance] CMObj.field CMObj.numberField CMObj.alg

theorem GlobalTheory.IndefiniteRowSideFullHecke.CMObjBundlePull.mem_psiBar_of_notMem_psi (H : Host E) (τ : E →+* ℂ) (h : τ ∉ psi H) : τ ∈ psiBar H := by sorry
