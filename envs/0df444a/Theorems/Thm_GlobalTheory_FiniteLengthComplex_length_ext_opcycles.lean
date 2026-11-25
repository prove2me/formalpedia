-- Prove2me | Theorems.Thm_GlobalTheory_FiniteLengthComplex_length_ext_opcycles
-- name    : GlobalTheory.FiniteLengthComplex.length_ext_opcycles
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T00:01:59.477513+00:00
-- url     : https://prove2.me/theorems/c870f740-9899-4b25-adbd-2ff58d78f17c
-- title:
--   Finite Length Complex: length ext opcycles
-- statement:
--   The Finite Length Complex construction uses the length ext opcycles property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/AcyclicityLemmaDepthDifferentialCokernelsFiniteL.lean#L204-L238
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/AcyclicityLemmaDepthDifferentialCokernelsFiniteL.lean#L204-L238

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

theorem GlobalTheory.FiniteLengthComplex.length_ext_opcycles (Y : ModuleCat.{0} R) (hP : ∀ i, Projective (C.X i)) (j : ℕ)
    (hH : ∀ i < j + 1, IsZero (C.homology i)) :
    Module.length R (Abelian.Ext.{0} (C.opcycles (j + 1)) Y (j + 1)) =
      Module.length R (Abelian.Ext.{0} (C.opcycles 0) Y 0 ⧸ LinearMap.range
        ((Ext.mk₀ (C.fromOpcycles 0 1)).precompOfLinear R Y (zero_add 0))) := by sorry
