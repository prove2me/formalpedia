-- Prove2me | Theorems.Thm_GlobalTheory_SW_LinChange_finsum_quot_map
-- name    : GlobalTheory.SW.LinChange.finsum_quot_map
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T19:41:18.979938+00:00
-- url     : https://prove2.me/theorems/116bbad6-9ddf-4d6e-ba9d-3c6f9b39a3a3
-- title:
--   Lin Change: finsum quot map
-- statement:
--   The Lin Change construction uses the finsum quot map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/SchwartzBruhatInvariantIntegralMatrixMul.lean#L35-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/SchwartzBruhatInvariantIntegralMatrixMul.lean#L35-L45

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

theorem GlobalTheory.SW.LinChange.finsum_quot_map {V : Type} [AddCommGroup V] (S : AddSubgroup V) (T : V ≃+ V)
    (φ : V → ℂ) (hφ : ∀ x, ∀ y ∈ S.map T.toAddMonoidHom, φ (x + y) = φ x) :
    ∑ᶠ q : V ⧸ S, φ (T q.out) = ∑ᶠ q : V ⧸ S.map T.toAddMonoidHom, φ q.out := by sorry
