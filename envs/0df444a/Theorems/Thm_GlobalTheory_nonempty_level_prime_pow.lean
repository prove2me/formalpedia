-- Prove2me | Theorems.Thm_GlobalTheory_nonempty_level_prime_pow
-- name    : GlobalTheory.nonempty_level_prime_pow
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:20:48.022182+00:00
-- url     : https://prove2.me/theorems/6b62de8a-cee0-4d65-a8e0-83e97bc9afb6
-- title:
--   Global Theory: nonempty level prime pow
-- statement:
--   The Global Theory construction uses the nonempty level prime pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaFamilyOrigin/ExistsIsSymplecticFamilySpan.lean#L244-L287
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaFamilyOrigin/ExistsIsSymplecticFamilySpan.lean#L244-L287

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DualRestrictSurjectiveOfIsTorsionFreeQuotient
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_WeilIsAlternatingSkewNatural
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_ExistsIsSymplecticFamilySpan
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory

theorem GlobalTheory.nonempty_level_prime_pow : Out.Laws → ∀ (K : Type) [Field K] [IsAlgClosed K]
    (P : PolAV (Spec (CommRingCat.of K))) (n J : ℕ), n.Prime → (n : K) ≠ 0 →
    ∀ ze : Γ(Spec (CommRingCat.of K), ⊤)ˣ, IsPrimitiveRoot ze (n ^ J) → Nonempty (Level P (n ^ J) ze) := by sorry
