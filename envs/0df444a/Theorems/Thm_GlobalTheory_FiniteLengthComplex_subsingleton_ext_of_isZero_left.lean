-- Prove2me | Theorems.Thm_GlobalTheory_FiniteLengthComplex_subsingleton_ext_of_isZero_left
-- name    : GlobalTheory.FiniteLengthComplex.subsingleton_ext_of_isZero_left
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T00:01:54.278127+00:00
-- url     : https://prove2.me/theorems/3ba54005-e2cb-4be9-988c-d43359bafb68
-- title:
--   Finite Length Complex: subsingleton ext of is Zero left
-- statement:
--   The Finite Length Complex construction uses the subsingleton ext of is Zero left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/AcyclicityLemmaDepthDifferentialCokernelsFiniteL.lean#L18-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/AcyclicityLemmaDepthDifferentialCokernelsFiniteL.lean#L18-L21

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

theorem GlobalTheory.FiniteLengthComplex.subsingleton_ext_of_isZero_left {X : ModuleCat.{0} R} (h : IsZero X) (Y : ModuleCat.{0} R)
    (n : ℕ) : Subsingleton (Abelian.Ext.{0} X Y n) := by sorry
