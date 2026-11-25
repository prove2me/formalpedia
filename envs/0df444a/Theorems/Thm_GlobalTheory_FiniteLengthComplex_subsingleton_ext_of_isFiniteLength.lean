-- Prove2me | Theorems.Thm_GlobalTheory_FiniteLengthComplex_subsingleton_ext_of_isFiniteLength
-- name    : GlobalTheory.FiniteLengthComplex.subsingleton_ext_of_isFiniteLength
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T00:01:26.233697+00:00
-- url     : https://prove2.me/theorems/e39e11e2-4e84-419b-8962-013d05805003
-- title:
--   Finite Length Complex: subsingleton ext of is Finite Length
-- statement:
--   The Finite Length Complex construction uses the subsingleton ext of is Finite Length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/AcyclicityLemmaDepthDifferentialCokernelsFiniteL.lean#L36-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/AcyclicityLemmaDepthDifferentialCokernelsFiniteL.lean#L36-L50

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

theorem GlobalTheory.FiniteLengthComplex.subsingleton_ext_of_isFiniteLength [IsLocalRing R] (Y : ModuleCat.{0} R) (n : ℕ)
    (hk : Subsingleton (Abelian.Ext.{0} (ModuleCat.of R (R ⧸ maximalIdeal R)) Y n))
    (M : Type) [AddCommGroup M] [Module R M] (hM : IsFiniteLength R M) :
    Subsingleton (Abelian.Ext.{0} (ModuleCat.of R M) Y n) := by sorry
