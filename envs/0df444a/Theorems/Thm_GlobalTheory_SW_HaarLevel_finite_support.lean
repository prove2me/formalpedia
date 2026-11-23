-- Prove2me | Theorems.Thm_GlobalTheory_SW_HaarLevel_finite_support
-- name    : GlobalTheory.SW.HaarLevel.finite_support
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:15:05.333097+00:00
-- url     : https://prove2.me/theorems/b4cbfc32-0c27-4772-854d-78bb71d2f44e
-- title:
--   Haar Level: finite support
-- statement:
--   The Haar Level construction uses the finite support property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/FinsumQuotientOfLe.lean#L111-L134
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/FinsumQuotientOfLe.lean#L111-L134

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_FinsumQuotientOfLe
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
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.HaarLevel
noncomputable section
open NumberField
variable {K : Type} [Field K] [NumberField K] {κ ι : Type} [Fintype κ] [Fintype ι]

theorem GlobalTheory.SW.HaarLevel.finite_support {R : ℕ} {φ : Matrix κ ι K → ℂ} (hR : 0 < R) (h : HasLevel R φ) :
    (Function.support fun q : Matrix κ ι K ⧸ perSub K κ ι R => φ q.out).Finite := by sorry
