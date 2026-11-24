-- Prove2me | Theorems.Thm_GlobalTheory_geomRegFib_of_isRegularRing_essFiniteType
-- name    : GlobalTheory.geomRegFib_of_isRegularRing_essFiniteType
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T22:54:13.903807+00:00
-- url     : https://prove2.me/theorems/efbe93a6-5b7c-4e82-a094-0adbab45ef7c
-- title:
--   Global Theory: geom Reg Fib of is Regular Ring ess Finite Type
-- statement:
--   The Global Theory construction uses the geom Reg Fib of is Regular Ring ess Finite Type property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/GeomRegFibOfIsRegularRingTensorEssFiniteType.lean#L8-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/GeomRegFibOfIsRegularRingTensorEssFiniteType.lean#L8-L16

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_FinalTheorems
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_FinTypeQE
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GeomRegFibOfIsRegularRingTensorEssFiniteType
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing TensorProduct ReciprocityTheory.AnForm.R
open GlobalTheory

theorem GlobalTheory.geomRegFib_of_isRegularRing_essFiniteType :
    ∀ (R B : Type) [CommRing R] [CommRing B] [Algebra R B],
      (∀ (K : Type) [Field K] [Algebra R K] [Algebra.EssFiniteType R K], IsRegularRing (B ⊗[R] K)) →
        FinalTheorems.GeomRegFib R B := by sorry
