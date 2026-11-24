-- Prove2me | Theorems.Thm_GlobalTheory_ChartQF_range_subset_stalk
-- name    : GlobalTheory.ChartQF.range_subset_stalk
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T11:09:11.09504+00:00
-- url     : https://prove2.me/theorems/7058bd3a-2f90-4e38-80f9-80b52bdc2989
-- title:
--   Chart QF: range subset stalk
-- statement:
--   The Chart QF construction uses the range subset stalk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsAlgebraicOfMemClosure.lean#L150-L167
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsAlgebraicOfMemClosure.lean#L150-L167

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsCompletedStrictHens
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsAlgebraicOfMemClosure
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ChartQF

theorem GlobalTheory.ChartQF.range_subset_stalk {F R : Type} [CommRing F] [CommRing R] [IsLocalRing R] {S : Scheme.{0}} (ξ : Sp R ⟶ S)
    (σ : S ⟶ Sp F) (b : F →+* R) (h : ξ ≫ σ = spMap b) :
    Set.range b ⊆ Set.range (Scheme.stalkClosedPointTo ξ).hom := by sorry
