-- Prove2me | Theorems.Thm_GlobalTheory_FiniteLengthComplex_length_ext_zero_quot
-- name    : GlobalTheory.FiniteLengthComplex.length_ext_zero_quot
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T00:03:25.841719+00:00
-- url     : https://prove2.me/theorems/f71ea45f-fae2-4b4d-acf9-d9dd3bfeb0df
-- title:
--   Finite Length Complex: length ext zero quot
-- statement:
--   The Finite Length Complex construction uses the length ext zero quot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/AcyclicityLemmaDepthDifferentialCokernelsFiniteL.lean#L240-L264
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/AcyclicityLemmaDepthDifferentialCokernelsFiniteL.lean#L240-L264

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

theorem GlobalTheory.FiniteLengthComplex.length_ext_zero_quot :
    Module.length R (Abelian.Ext.{0} (C.opcycles 0) (ModuleCat.of R R) 0 ⧸ LinearMap.range
        ((Ext.mk₀ (C.fromOpcycles 0 1)).precompOfLinear R (ModuleCat.of R R) (zero_add 0))) =
      Module.length R (Module.Dual R (C.X 0) ⧸ LinearMap.range (C.d 0 1).hom.dualMap) := by sorry
