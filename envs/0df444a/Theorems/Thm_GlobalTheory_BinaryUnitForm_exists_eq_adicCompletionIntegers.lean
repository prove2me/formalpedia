-- Prove2me | Theorems.Thm_GlobalTheory_BinaryUnitForm_exists_eq_adicCompletionIntegers
-- name    : GlobalTheory.BinaryUnitForm.exists_eq_adicCompletionIntegers
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T13:28:43.835397+00:00
-- url     : https://prove2.me/theorems/0613d266-8db8-4f33-928c-4e469ad5d6d1
-- title:
--   Binary Unit Form: exists eq adic Completion Integers
-- statement:
--   The Binary Unit Form construction uses the exists eq adic Completion Integers property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ExistsEqAdicCompletionIntegers.lean#L40-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ExistsEqAdicCompletionIntegers.lean#L40-L47

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsEqTransposeMulMapOfIdempotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_FiniteResidueFieldAdicCompletionIntegers
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsEqAdicCompletionIntegers
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsDedekindDomain NumberField IsLocalRing
open GlobalTheory GlobalTheory.BinaryUnitForm

theorem GlobalTheory.BinaryUnitForm.exists_eq_adicCompletionIntegers : ∀ (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (t n u : v.adicCompletionIntegers F),
    IsUnit (t ^ 2 - 4 * n) → IsUnit u → ∃ r s : v.adicCompletionIntegers F,
      r ^ 2 + t * r * s + n * s ^ 2 = u := by sorry
