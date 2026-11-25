-- Prove2me | Theorems.Thm_GlobalTheory_BigOn_on_of_onWith_canonical
-- name    : GlobalTheory.BigOn.on_of_onWith_canonical
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T17:33:51.996118+00:00
-- url     : https://prove2.me/theorems/9e74775e-ccc2-5c6d-bb37-722c42927ec1
-- title:
--   Big On: on of on With canonical
-- statement:
--   The Big On construction uses the on of on With canonical property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/OnOfOnWithCanonical.lean#L63-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/OnOfOnWithCanonical.lean#L63-L73

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefiniteTree_ExampleSatisfiesConditionsAtFive
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_OnOfOnWithCanonical
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Formalism.L2.Indef Formalism.L2.Indef.Tree
open GlobalTheory GlobalTheory.BigOn

theorem GlobalTheory.BigOn.on_of_onWith_canonical :
    ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (Bs : DefBase K) (Df : DefSide Bs) (S : IndefData Df) (Z : IndefScale Bs) (C C' CH CH' : ℝ) (err : HeightOneSpectrum (𝓞 K) → Bs.J → ℝ), 0 < S.D → 0 ≤ Z.E1u → 2 * C ≤ C' → (∀ w ∈ S.Tw, ∀ j, 0 ≤ Z.J0 (S.μ w) w j) → (∀ w j, S.err0 w j = max 0 ((∑ j', ((S.Iw j' (S.μ w) w : ℝ) + (S.Iw j' (S.μ w) (Formalism.DivisionValues.conjPl w) : ℝ))) / (S.D : ℝ) - ∑ j', 2 * ((Formalism.EigenvalueLevelCeiling.ramw w : ℝ) * Z.F0 w j') - (Formalism.EigenvalueLevelCeiling.ramw w : ℝ) * (2 / (Formalism.EigenvalueLevelCeiling.plc w : ℝ) ^ 2)) / ((Formalism.EigenvalueLevelCeiling.ramw w : ℝ) * (Fintype.card Bs.J : ℝ))) → ONwith S (Z.num C CH) err → S.ON (Z.num C' CH') := by sorry
