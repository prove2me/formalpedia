-- Prove2me | Theorems.Thm_GlobalTheory_DerLin_le_of_fst_eq
-- name    : GlobalTheory.DerLin.le_of_fst_eq
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T20:11:36.299308+00:00
-- url     : https://prove2.me/theorems/6c797d65-f7dd-4ee3-8509-04aeb8eb9bcd
-- title:
--   Der Lin: le of fst eq
-- statement:
--   The Der Lin construction uses the le of fst eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/IsCombAtIffIsDerivAt0.lean#L39-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/IsCombAtIffIsDerivAt0.lean#L39-L48

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExponentialDerivativeAtZeroIsTangentStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_DerivativeAlongTangentCombinationModuliStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsTangentModuleUniversalGroupStatement
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_UnivFrame
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_NormConst
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CuspFree
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RdOrbIntOfLatZ
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AllTest
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Landherr__ExistsNormTensor_9eff20d6b37353d0
import Definitions.Def_Development_AbelianVarietyTheory_Statements_HyperbolicHypotheses_HypothesesInhabitedHyperbolic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsCombAtIffIsDerivAt0
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors
open GlobalTheory GlobalTheory.DerLin

theorem GlobalTheory.DerLin.le_of_fst_eq {S : Type} [CommRing S] {X : Scheme.{0}} {v v' : Sp (DualNumber S) ⟶ X}
    (hh : spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ v = spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ v')
    {U : X.Opens} (h : ⊤ ≤ v' ⁻¹ᵁ U) : ⊤ ≤ v ⁻¹ᵁ U := by sorry
