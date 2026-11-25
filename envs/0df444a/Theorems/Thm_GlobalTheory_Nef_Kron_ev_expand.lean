-- Prove2me | Theorems.Thm_GlobalTheory_Nef_Kron_ev_expand
-- name    : GlobalTheory.Nef.Kron.ev_expand
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T00:59:00.670204+00:00
-- url     : https://prove2.me/theorems/e907949e-d5da-4f5a-b1cd-8303326bf710
-- title:
--   Kron: ev expand
-- statement:
--   The Kron construction uses the ev expand property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsRatOfHankelEventuallyZero.lean#L22-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsRatOfHankelEventuallyZero.lean#L22-L28

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

theorem GlobalTheory.Nef.Kron.ev_expand (q p : F[X]) (n : ℕ) (hp : p.natDegree < n) :
    ev c (q * p) = ∑ j ∈ Finset.range n, p.coeff j * ev c (q * X ^ j) := by sorry
