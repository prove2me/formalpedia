-- Prove2me | Theorems.Thm_GlobalTheory_FiniteLengthComplex_shortExact_submodule
-- name    : GlobalTheory.FiniteLengthComplex.shortExact_submodule
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T00:02:37.743936+00:00
-- url     : https://prove2.me/theorems/3dffb8a4-4dd7-4d15-aa70-d8c803367b29
-- title:
--   Finite Length Complex: short Exact submodule
-- statement:
--   The Finite Length Complex construction uses the short Exact submodule property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/AcyclicityLemmaDepthDifferentialCokernelsFiniteL.lean#L23-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/AcyclicityLemmaDepthDifferentialCokernelsFiniteL.lean#L23-L27

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsRegularOfSupportDimQuotientAddLengthLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_AcyclicityLemmaDepthDifferentialCokernelsFiniteL
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian IsLocalRing
open GlobalTheory
open GlobalTheory.FiniteLengthComplex
variable {R : Type} [CommRing R]

theorem GlobalTheory.FiniteLengthComplex.shortExact_submodule {M : Type} [AddCommGroup M] [Module R M] (N : Submodule R M) :
    (ModuleCat.shortComplexOfCompEqZero N.subtype N.mkQ
      (LinearMap.exact_subtype_mkQ N).linearMap_comp_eq_zero).ShortExact := by sorry
