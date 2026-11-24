-- Prove2me | Theorems.Thm_GlobalTheory_SW_heisS_exists_den
-- name    : GlobalTheory.SW.heisS_exists_den
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T19:45:31.1546+00:00
-- url     : https://prove2.me/theorems/9563def0-1cc1-445e-bc68-bdeab166a91f
-- title:
--   SW: heis S exists den
-- statement:
--   The SW construction uses the heis S exists den property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/HeisenbergOperatorRationalPointLaws.lean#L10-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/HeisenbergOperatorRationalPointLaws.lean#L10-L24

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_RationalSchwartzBruhatAlgebraIntegralLinearStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HeisenbergOperatorRationalPointLaws
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
open GlobalTheory GlobalTheory.SW

theorem GlobalTheory.SW.heisS_exists_den {κ ι : Type} [Fintype κ] [Fintype ι] (a : Matrix κ ι ℚ) :
    ∃ D : ℕ, 0 < D ∧ ∀ k i, IsIntegral ℤ ((D : ℚ) * a k i) := by sorry
