-- Prove2me | Theorems.Thm_GlobalTheory_SW_LinChange_finsum_prod_fst
-- name    : GlobalTheory.SW.LinChange.finsum_prod_fst
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T19:41:54.776097+00:00
-- url     : https://prove2.me/theorems/52a3c995-39a7-4a29-a2c9-030b593e97a0
-- title:
--   Lin Change: finsum prod fst
-- statement:
--   The Lin Change construction uses the finsum prod fst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/SchwartzBruhatInvariantIntegralMatrixMul.lean#L8-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/SchwartzBruhatInvariantIntegralMatrixMul.lean#L8-L20

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SchwartzBruhatInvariantIntegralMatrixMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.LinChange

theorem GlobalTheory.SW.LinChange.finsum_prod_fst {A B : Type} [Finite B] [Nonempty B] (g : A → ℂ) :
    ∑ᶠ p : A × B, g p.1 = (Nat.card B : ℂ) * ∑ᶠ a, g a := by sorry
