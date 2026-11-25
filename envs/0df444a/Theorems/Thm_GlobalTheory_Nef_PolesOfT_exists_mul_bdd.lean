-- Prove2me | Theorems.Thm_GlobalTheory_Nef_PolesOfT_exists_mul_bdd
-- name    : GlobalTheory.Nef.PolesOfT.exists_mul_bdd
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T01:01:46.508585+00:00
-- url     : https://prove2.me/theorems/d65362db-e279-4bbf-aa3a-aae44d12b45a
-- title:
--   Poles Of T: exists mul bdd
-- statement:
--   The Poles Of T construction uses the exists mul bdd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsManyBoundedByPow.lean#L69-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsManyBoundedByPow.lean#L69-L126

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsAdmissibleIntegralBasisChangeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsManyBoundedByPow
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
open GlobalTheory GlobalTheory.Nef GlobalTheory.Nef.PolesOfT
open Polynomial
variable {k F : Type} [Field k] [Field F] [Algebra k F]

theorem GlobalTheory.Nef.PolesOfT.exists_mul_bdd (t y : F) (hy : IsAlgebraic k⟮t⟯ y) :
    ∃ q : k[X], aeval t q ≠ 0 ∧ ∃ c : ℕ, ∀ v : Place k F, v.1 (aeval t q * y) ≤ Mx t v ^ c := by sorry
