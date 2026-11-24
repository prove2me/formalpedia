-- Prove2me | Theorems.Thm_GlobalTheory_linIndep_intBilinForm_charZero_comb_eq_zero
-- name    : GlobalTheory.linIndep_intBilinForm_charZero_comb_eq_zero
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T23:06:56.373298+00:00
-- url     : https://prove2.me/theorems/141b1ac1-6c44-4c1e-ac44-181e064fe5cd
-- title:
--   Global Theory: lin Indep int Bilin Form char Zero comb eq zero
-- statement:
--   The Global Theory construction uses the lin Indep int Bilin Form char Zero comb eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LinIndepIntBilinFormCharZeroCombinationEqZero.lean#L5-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LinIndepIntBilinFormCharZeroCombinationEqZero.lean#L5-L37

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LinIndepIntBilinFormCharZeroCombinationEqZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory

theorem GlobalTheory.linIndep_intBilinForm_charZero_comb_eq_zero
    {X : Type} [AddCommGroup X] {m : ℕ} (gam : Fin m → LinearMap.BilinForm ℤ X)
    (k : Type) [Field k] [CharZero k] (a : Fin m → k) :
    LinearIndependent ℤ gam → (∀ y z, ∑ i, a i * (gam i y z : k) = 0) → a = 0 := by sorry
