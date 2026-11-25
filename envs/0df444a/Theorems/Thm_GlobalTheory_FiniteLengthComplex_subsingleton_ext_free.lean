-- Prove2me | Theorems.Thm_GlobalTheory_FiniteLengthComplex_subsingleton_ext_free
-- name    : GlobalTheory.FiniteLengthComplex.subsingleton_ext_free
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T00:03:12.43482+00:00
-- url     : https://prove2.me/theorems/171b206d-9edd-45e7-acca-417e8f85f5d1
-- title:
--   Finite Length Complex: subsingleton ext free
-- statement:
--   The Finite Length Complex construction uses the subsingleton ext free property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/AcyclicityLemmaDepthDifferentialCokernelsFiniteL.lean#L95-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/AcyclicityLemmaDepthDifferentialCokernelsFiniteL.lean#L95-L108

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

theorem GlobalTheory.FiniteLengthComplex.subsingleton_ext_free (X : ModuleCat.{0} R) (n : ℕ)
    (h : Subsingleton (Abelian.Ext.{0} X (ModuleCat.of R R) n))
    (F : ModuleCat.{0} R) [Module.Free R F] [Module.Finite R F] :
    Subsingleton (Abelian.Ext.{0} X F n) := by sorry
