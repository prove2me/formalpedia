-- Prove2me | Theorems.Thm_GlobalTheory_MinorGerm_sum_range_ite
-- name    : GlobalTheory.MinorGerm.sum_range_ite
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T00:44:41.011806+00:00
-- url     : https://prove2.me/theorems/996aa946-c8bd-47dc-966f-6dbb648e68b7
-- title:
--   Minor Germ: sum range ite
-- statement:
--   The Minor Germ construction uses the sum range ite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ProdFactorialDiag.lean#L264-L271
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ProdFactorialDiag.lean#L264-L271

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BiadditiveInSingleVariables
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_LegendreAndCapelli
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ProdFactorialDiag
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds
noncomputable section
open GlobalTheory GlobalTheory.MinorGerm
variable {C : Type} [Field C] {σ : Type} {N N' : ℕ}

theorem GlobalTheory.MinorGerm.sum_range_ite {M : Type} [AddCommMonoid M] {k : ℕ} (hk : k ≤ N) (F : ℕ → M) :
    ∑ ρ ∈ Finset.range N, (if ρ < k then F ρ else 0) = ∑ ρ ∈ Finset.range k, F ρ := by sorry
