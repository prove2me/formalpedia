-- Prove2me | Theorems.Thm_GlobalTheory_Reg_ChartInt_vV_unit
-- name    : GlobalTheory.Reg.ChartInt.vV_unit
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T11:28:23.416782+00:00
-- url     : https://prove2.me/theorems/4ab85eb9-4549-4512-9e42-db943fdf2d89
-- title:
--   Chart Int: v V unit
-- statement:
--   The Chart Int construction uses the v V unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/IntegralityTrivialValuationsOfNormalAffineCharts.lean#L35-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/IntegralityTrivialValuationsOfNormalAffineCharts.lean#L35-L40

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RegModelC
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_RegularCharts_SCharts
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_FrameCharts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RegQFree
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_FnTrdegOf
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RealPtGeo
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IntAllProofFree
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_IntegralityTrivialValuationsOfNormalAffineCharts
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg
noncomputable section
open GlobalTheory GlobalTheory.Reg GlobalTheory.Reg.ChartInt
open IsLocalRing Formalism.L2.PjFree
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]

theorem GlobalTheory.Reg.ChartInt.vV_unit (u : V) (hu : u ∉ maximalIdeal V) : vV V (algebraMap V (FractionRing V) u) = 0 := by sorry
