-- Prove2me | Theorems.Thm_GlobalTheory_FiniteLengthComplex_length_ext_of_isFiniteLength
-- name    : GlobalTheory.FiniteLengthComplex.length_ext_of_isFiniteLength
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T00:01:36.385817+00:00
-- url     : https://prove2.me/theorems/d27b6272-f659-4c61-9b4e-441a4f295e9c
-- title:
--   Finite Length Complex: length ext of is Finite Length
-- statement:
--   The Finite Length Complex construction uses the length ext of is Finite Length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/AcyclicityLemmaDepthDifferentialCokernelsFiniteL.lean#L52-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/AcyclicityLemmaDepthDifferentialCokernelsFiniteL.lean#L52-L93

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

theorem GlobalTheory.FiniteLengthComplex.length_ext_of_isFiniteLength [IsLocalRing R] (Y : ModuleCat.{0} R) (g : ℕ)
    (hk : ∀ n, n ≠ g →
      Subsingleton (Abelian.Ext.{0} (ModuleCat.of R (R ⧸ maximalIdeal R)) Y n))
    (M : Type) [AddCommGroup M] [Module R M] (hM : IsFiniteLength R M) :
    Module.length R (Abelian.Ext.{0} (ModuleCat.of R M) Y g) = Module.length R M *
      Module.length R (Abelian.Ext.{0} (ModuleCat.of R (R ⧸ maximalIdeal R)) Y g) := by sorry
