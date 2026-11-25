-- Prove2me | Theorems.Thm_GlobalTheory_FiniteLengthComplex_opcyclesShortComplex_shortExact
-- name    : GlobalTheory.FiniteLengthComplex.opcyclesShortComplex_shortExact
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T00:01:46.855656+00:00
-- url     : https://prove2.me/theorems/4f5cea82-6511-43e3-9ebf-3ec7a820ee55
-- title:
--   Finite Length Complex: opcycles Short Complex short Exact
-- statement:
--   The Finite Length Complex construction uses the opcycles Short Complex short Exact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/AcyclicityLemmaDepthDifferentialCokernelsFiniteL.lean#L143-L166
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/AcyclicityLemmaDepthDifferentialCokernelsFiniteL.lean#L143-L166

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
variable (C : CochainComplex (ModuleCat.{0} R) ℕ)

theorem GlobalTheory.FiniteLengthComplex.opcyclesShortComplex_shortExact (i : ℕ) (h : IsZero (C.homology i)) :
    (opcyclesShortComplex C i).ShortExact := by sorry
