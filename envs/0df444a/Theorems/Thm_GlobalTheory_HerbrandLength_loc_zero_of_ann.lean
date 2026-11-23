-- Prove2me | Theorems.Thm_GlobalTheory_HerbrandLength_loc_zero_of_ann
-- name    : GlobalTheory.HerbrandLength.loc_zero_of_ann
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:56:42.593017+00:00
-- url     : https://prove2.me/theorems/6f948b87-d4f9-4134-92b3-e087ce181837
-- title:
--   Herbrand Length: loc zero of ann
-- statement:
--   The Herbrand Length construction uses the loc zero of ann property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LengthCokerLsmulEqLengthKerAddSum.lean#L27-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LengthCokerLsmulEqLengthKerAddSum.lean#L27-L31

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LengthEqKerAddRange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LengthCokerLsmulEqLengthKerAddSum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.HerbrandLength
open IsLocalRing
variable {A : Type} [CommRing A]

theorem GlobalTheory.HerbrandLength.loc_zero_of_ann (p : Ideal A) [p.IsPrime] (M : Type) [AddCommGroup M] [Module A M]
    (s : A) (hs : s ∉ p) (hsM : ∀ x : M, s • x = 0) :
    Module.length (Localization.AtPrime p) (LocalizedModule p.primeCompl M) = 0 := by sorry
