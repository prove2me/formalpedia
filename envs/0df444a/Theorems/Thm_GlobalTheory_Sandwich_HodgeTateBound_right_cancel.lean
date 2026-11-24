-- Prove2me | Theorems.Thm_GlobalTheory_Sandwich_HodgeTateBound_right_cancel
-- name    : GlobalTheory.Sandwich.HodgeTateBound.right_cancel
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T19:45:45.630952+00:00
-- url     : https://prove2.me/theorems/0888bbad-26f0-4e32-9f06-42fa92dea2f7
-- title:
--   Hodge Tate Bound: right cancel
-- statement:
--   The Hodge Tate Bound construction uses the right cancel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SmulMemRange.lean#L15-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SmulMemRange.lean#L15-L29

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

theorem GlobalTheory.Sandwich.HodgeTateBound.right_cancel [IsDomain A] {F G : Matrix (Fin h) (Fin h) A} {μ : A} (hμ : μ ≠ 0)
    (hGF : G * F = μ • (1 : Matrix (Fin h) (Fin h) A)) {X Y : Matrix (Fin h) (Fin h) A}
    (hX : X * F = Y * F) : X = Y := by sorry
