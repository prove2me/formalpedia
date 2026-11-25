-- Prove2me | Theorems.Thm_GlobalTheory_Nef_Kron_ev_top
-- name    : GlobalTheory.Nef.Kron.ev_top
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T01:00:28.881026+00:00
-- url     : https://prove2.me/theorems/73c20e52-d5eb-4aa4-bc30-42e0d8ad9139
-- title:
--   Kron: ev top
-- statement:
--   The Kron construction uses the ev top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsRatOfHankelEventuallyZero.lean#L35-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsRatOfHankelEventuallyZero.lean#L35-L38

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

theorem GlobalTheory.Nef.Kron.ev_top (q p : F[X]) (s : ℕ) (h : ∀ j < s, ev c (q * X ^ j) = 0)
    (hp : p.natDegree ≤ s) : ev c (q * p) = p.coeff s * ev c (q * X ^ s) := by sorry
