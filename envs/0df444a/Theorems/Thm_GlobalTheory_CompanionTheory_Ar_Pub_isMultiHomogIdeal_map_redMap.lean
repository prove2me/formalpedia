-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Pub_isMultiHomogIdeal_map_redMap
-- name    : GlobalTheory.CompanionTheory.Ar.Pub.isMultiHomogIdeal_map_redMap
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T11:21:43.960597+00:00
-- url     : https://prove2.me/theorems/f92c53a4-30e9-461e-b474-95ef3def2579
-- title:
--   Pub: is Multi Homog Ideal map red Map
-- statement:
--   The Pub construction uses the is Multi Homog Ideal map red Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/AlgebraProofs/IsMultiHomogIdealMapRedMap.lean#L58-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/AlgebraProofs/IsMultiHomogIdealMapRedMap.lean#L58-L64

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterNamed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRes
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_BlowupProjections_BlowupProjStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_RationalSections_ThmISt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MixedFieldContraction_ContractMixedFieldStatement
import Definitions.Def_P2M_Def_Development_AutomorphicSpectrum_PublishedTheorems_Metrics__PoincareLelong_e61d89ea90cf58ae
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_IsMultiHomogIdealMapRedMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Pub
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

theorem GlobalTheory.CompanionTheory.Ar.Pub.isMultiHomogIdeal_map_redMap {p : ℕ} {W : Ideal (MRing ι)} (h : IsMultiHomogIdeal W) :
    IsMultiHomogIdeal (W.map (redMap ι p)) := by sorry
