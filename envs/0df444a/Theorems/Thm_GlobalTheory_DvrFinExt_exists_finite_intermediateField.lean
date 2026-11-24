-- Prove2me | Theorems.Thm_GlobalTheory_DvrFinExt_exists_finite_intermediateField
-- name    : GlobalTheory.DvrFinExt.exists_finite_intermediateField
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T12:52:29.648007+00:00
-- url     : https://prove2.me/theorems/97dbfd5f-0741-4b70-b7f0-86fdffacf605
-- title:
--   Dvr Fin Ext: exists finite intermediate Field
-- statement:
--   The Dvr Fin Ext construction uses the exists finite intermediate Field property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsFiniteExtensionCompleteDvrPadicAlgCl.lean#L8-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsFiniteExtensionCompleteDvrPadicAlgCl.lean#L8-L31

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsCompleteDvrIntegralClosureFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitBallEqOfIntegralDvr
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsFiniteExtensionCompleteDvrPadicAlgCl
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory GlobalTheory.DvrFinExt

theorem GlobalTheory.DvrFinExt.exists_finite_intermediateField (F K Ω : Type) [Field F] [Field K] [Field Ω] [Algebra F Ω]
    [Algebra.IsIntegral F Ω] [Algebra K Ω] (hQ : ∀ q : F, algebraMap F Ω q ∈ (algebraMap K Ω).range)
    (R : Type) [CommRing R] [Algebra.FiniteType ℤ R] (y₀ : R →+* Ω) :
    ∃ L : IntermediateField K Ω, FiniteDimensional K L ∧ ∀ a, y₀ a ∈ L := by sorry
