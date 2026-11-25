-- Prove2me | Theorems.Thm_GlobalTheory_Sandwich_HodgeTateBound_mul_swap
-- name    : GlobalTheory.Sandwich.HodgeTateBound.mul_swap
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:30:00.547859+00:00
-- url     : https://prove2.me/theorems/1004e216-6b13-4078-9dfe-5acf3c3a7260
-- title:
--   Hodge Tate Bound: mul swap
-- statement:
--   The Hodge Tate Bound construction uses the mul swap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SmulMemRange.lean#L31-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SmulMemRange.lean#L31-L36

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_CotangentSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_CyclicRecursionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_XiMulNu
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FontaineAinfLocalDomainXiAdicOrderStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SmulMemRange
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.PGsh.Up GlobalTheory.Sandwich Matrix
open GlobalTheory GlobalTheory.Sandwich GlobalTheory.Sandwich.HodgeTateBound
variable {A O : Type} [CommRing A] [CommRing O] {h : ℕ}

theorem GlobalTheory.Sandwich.HodgeTateBound.mul_swap [IsDomain A] {F G : Matrix (Fin h) (Fin h) A} {μ : A} (hμ : μ ≠ 0)
    (hGF : G * F = μ • (1 : Matrix (Fin h) (Fin h) A)) :
    F * G = μ • (1 : Matrix (Fin h) (Fin h) A) := by sorry
