-- Prove2me | Theorems.Thm_GlobalTheory_Nef_Kron_isRat_of_ann
-- name    : GlobalTheory.Nef.Kron.isRat_of_ann
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T01:00:50.642713+00:00
-- url     : https://prove2.me/theorems/fecfa7ab-36e7-43a5-84b6-b3e8fac4f233
-- title:
--   Kron: is Rat of ann
-- statement:
--   The Kron construction uses the is Rat of ann property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsRatOfHankelEventuallyZero.lean#L140-L169
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsRatOfHankelEventuallyZero.lean#L140-L169

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsAdmissibleIntegralBasisChangeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsRatOfHankelEventuallyZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Nef GlobalTheory.Nef.Kron
open Polynomial
variable {F : Type} [Field F] (c : ℕ → F)

theorem GlobalTheory.Nef.Kron.isRat_of_ann (φ : PowerSeries F) (q : F[X]) (hq : q ≠ 0)
    (h : ∀ j, ev (fun i => PowerSeries.coeff i φ) (q * X ^ j) = 0) : IsRat φ := by sorry
