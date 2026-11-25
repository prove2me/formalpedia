-- Prove2me | Theorems.Thm_GlobalTheory_ChartQF_eq_spMap_of_injective
-- name    : GlobalTheory.ChartQF.eq_spMap_of_injective
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T11:58:18.341075+00:00
-- url     : https://prove2.me/theorems/12720a17-45ec-45ac-833a-9937cdd2c8fe
-- title:
--   Chart QF: eq sp Map of injective
-- statement:
--   The Chart QF construction uses the eq sp Map of injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsAlgebraicOfMemClosure.lean#L169-L181
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsAlgebraicOfMemClosure.lean#L169-L181

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

theorem GlobalTheory.ChartQF.eq_spMap_of_injective {F R K : Type} [CommRing F] [CommRing R] [CommRing K] (u : R →+* K)
    (hu : Function.Injective u) (σ : Sp R ⟶ Sp F) (b : F →+* R) (h : spMap u ≫ σ = spMap u ≫ spMap b) :
    σ = spMap b := by sorry
