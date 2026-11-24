-- Prove2me | Theorems.Thm_GlobalTheory_NormSheaf_normIdeal_map_away
-- name    : GlobalTheory.NormSheaf.normIdeal_map_away
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T19:42:58.271645+00:00
-- url     : https://prove2.me/theorems/4796ae93-58b9-4d5a-93e0-698b1fabbce5
-- title:
--   Norm Sheaf: norm Ideal map away
-- statement:
--   The Norm Sheaf construction uses the norm Ideal map away property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NormFormCoefficientIdealMapLocalizationAway.lean#L32-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NormFormCoefficientIdealMapLocalizationAway.lean#L32-L94

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FamIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormFormCoefficientIdealMapLocalizationAway
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits
open GlobalTheory GlobalTheory.NormSheaf

theorem GlobalTheory.NormSheaf.normIdeal_map_away : ∀ (A K L B A' B' : Type) [CommRing A] [CommRing B] [CommRing A'] [CommRing B'] [Field K] [Field L]
    [Algebra K L] [FiniteDimensional K L] [Algebra A K] [Algebra B L] [Algebra A' K] [Algebra B' L]
    [Algebra A A'] [Algebra B B'] [Algebra A B] (f : A) [IsLocalization.Away f A']
    [IsLocalization.Away (algebraMap A B f) B'],
    (algebraMap A' K).comp (algebraMap A A') = algebraMap A K →
    (algebraMap B' L).comp (algebraMap B B') = algebraMap B L →
    (algebraMap K L).comp (algebraMap A K) = (algebraMap B L).comp (algebraMap A B) →
    Function.Injective (algebraMap A' K) →
    (∀ {m : ℕ} (g : Fin m → B) s,
      (GlobalTheory.NormSheaf.normForm K L (fun i => algebraMap B L (g i))).coeff s ∈ (algebraMap A K).range) →
    ∀ J : Ideal B, (GlobalTheory.NormSheaf.normIdeal A K L B J).map (algebraMap A A') =
      GlobalTheory.NormSheaf.normIdeal A' K L B' (J.map (algebraMap B B')) := by sorry
