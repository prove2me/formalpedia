-- Prove2me | Theorems.Thm_GlobalTheory_of_isPullback_openCover
-- name    : GlobalTheory.of_isPullback_openCover
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T23:13:05.876259+00:00
-- url     : https://prove2.me/theorems/f5222c2f-bac1-44a1-91ae-e43f64974fc9
-- title:
--   Global Theory: of is Pullback open Cover
-- statement:
--   The Global Theory construction uses the of is Pullback open Cover property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FiniteFlatSurjectiveClosedSubschemeOfOpenCover.lean#L23-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FiniteFlatSurjectiveClosedSubschemeOfOpenCover.lean#L23-L32

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FiniteFlatSurjectiveClosedSubschemeOfOpenCover
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory

theorem GlobalTheory.of_isPullback_openCover (P : MorphismProperty Scheme.{0}) [IsZariskiLocalAtTarget P]
    {B T : Scheme.{0}} (f : B ⟶ T) {ι : Type} (V : ι → T.Opens) (hV : iSup V = ⊤)
    (A : ι → Scheme.{0}) (k : ∀ i, A i ⟶ B) (g : ∀ i, A i ⟶ (V i).toScheme)
    (h : ∀ i, IsPullback (k i) (g i) f (V i).ι) (hg : ∀ i, P (g i)) : P f := by sorry
