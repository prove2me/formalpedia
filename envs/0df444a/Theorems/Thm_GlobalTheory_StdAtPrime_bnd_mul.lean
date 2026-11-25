-- Prove2me | Theorems.Thm_GlobalTheory_StdAtPrime_bnd_mul
-- name    : GlobalTheory.StdAtPrime.bnd_mul
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:24:05.848801+00:00
-- url     : https://prove2.me/theorems/e584312c-e14b-5a7a-a73f-283e93f0b0e7
-- title:
--   Std At Prime: bnd mul
-- statement:
--   The Std At Prime construction uses the bnd mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/BndMul.lean#L13-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/BndMul.lean#L13-L27

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_BndMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open GlobalTheory GlobalTheory.StdAtPrime
variable {E : Type} [Field E] [NumberField E]

theorem GlobalTheory.StdAtPrime.bnd_mul (p n : ℕ) (A B : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E)) (hA : Bnd p A) (hB : Bnd p B) :
    Bnd p (A * B) := by sorry
