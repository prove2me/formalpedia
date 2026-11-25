-- Prove2me | Theorems.Thm_GlobalTheory_HolomorphicArc_nsmul_mem
-- name    : GlobalTheory.HolomorphicArc.nsmul_mem
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:07:54.136302+00:00
-- url     : https://prove2.me/theorems/9de92844-beed-5fb3-8135-6d076db83c5e
-- title:
--   Holomorphic Arc: nsmul mem
-- statement:
--   The Holomorphic Arc construction uses the nsmul mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/IsHolToHalfPlaneMono.lean#L25-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/IsHolToHalfPlaneMono.lean#L25-L31

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HasArcDataIff
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_OneArc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IsHolToHalfPlaneMono
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped LaurentSeries
open GlobalTheory GlobalTheory.HolomorphicArc
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}

theorem GlobalTheory.HolomorphicArc.nsmul_mem (v : D.La) : l.M • v ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La) := by sorry
