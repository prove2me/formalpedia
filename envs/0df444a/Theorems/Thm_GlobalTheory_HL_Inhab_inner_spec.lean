-- Prove2me | Theorems.Thm_GlobalTheory_HL_Inhab_inner_spec
-- name    : GlobalTheory.HL.Inhab.inner_spec
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T07:32:06.537637+00:00
-- url     : https://prove2.me/theorems/8f9c97bb-4a85-497e-af2a-81068dde2acb
-- title:
--   Inhab: inner spec
-- statement:
--   The Inhab construction uses the inner spec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermitianFourInverseMul.lean#L79-L217
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermitianFourInverseMul.lean#L79-L217

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsIntegralIff
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianFourInverseMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.Inhab
open GlobalTheory.HL.Model
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)

theorem GlobalTheory.HL.Inhab.inner_spec (g : Fin (r + 1) → S.V) (gs : Fin r → S.V) (Λ : Submodule L.O S.V)
    (hg : ∀ a (j : Fin r), hf L S.Hm (g a) (g j.castSucc) = 0)
    (hd : ∀ a j, hf L S.Hm (g a) (gs j) = if a = j.castSucc then 1 else 0)
    (hi : ∀ i j, hf L S.Hm (gs i) (gs j) = 0)
    (hΛ : IsSD L S.Hm Λ) (hgΛ : ∀ a, g a ∈ Λ) (hsΛ : ∀ j, gs j ∈ Λ)
    (c : E) (hc : c ∈ L.O) (hcz : c * hf L S.Hm (g (Fin.last r)) (g (Fin.last r)) = 1) :
    S.IsInner g gs (innerOf S g gs Λ) ∧ Λ = S.stdLat g gs (innerOf S g gs Λ) := by sorry
