-- Prove2me | Theorems.Thm_GlobalTheory_QuadraticZeta_discr_eq
-- name    : GlobalTheory.QuadraticZeta.discr_eq
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T19:12:14.270808+00:00
-- url     : https://prove2.me/theorems/51cf1f97-f3df-431e-b371-bcb41b82f1d4
-- title:
--   Quadratic Zeta: discr eq
-- statement:
--   The Quadratic Zeta construction uses the discr eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsIsKroneckerCharOfDiscr.lean#L23-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsIsKroneckerCharOfDiscr.lean#L23-L40

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsIsKroneckerCharOfDiscr
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
open scoped NumberTheorySymbols
open GlobalTheory GlobalTheory.QuadraticZeta
variable {R : Type*} [CommRing R]

theorem GlobalTheory.QuadraticZeta.discr_eq (b : Basis (Fin 2) ℤ R) (h0 : b 0 = 1) {t n : ℤ} (hw : b 1 ^ 2 = t * b 1 - n) :
    Algebra.discr ℤ b = t ^ 2 - 4 * n := by sorry
