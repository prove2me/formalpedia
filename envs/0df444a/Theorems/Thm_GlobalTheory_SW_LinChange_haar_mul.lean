-- Prove2me | Theorems.Thm_GlobalTheory_SW_LinChange_haar_mul
-- name    : GlobalTheory.SW.LinChange.haar_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:09:57.798534+00:00
-- url     : https://prove2.me/theorems/fb518474-3903-4317-919c-fe3b8af031a2
-- title:
--   Lin Change: haar mul
-- statement:
--   The Lin Change construction uses the haar mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/SchwartzBruhatInvariantIntegralMatrixMul.lean#L264-L274
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/SchwartzBruhatInvariantIntegralMatrixMul.lean#L264-L274

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
variable {K : Type} [Field K] [NumberField K] {κ ι : Type} [Fintype κ] [Fintype ι]

theorem GlobalTheory.SW.LinChange.haar_mul : ∀ (K κ ι : Type) [Field K] [NumberField K] [Fintype κ] [Fintype ι] [DecidableEq ι] [DecidableEq κ] (φ : Matrix κ ι K → ℂ), IsSB φ → (∀ A : Matrix ι ι K, A.det ≠ 0 → IsSB (fun x : Matrix κ ι K => φ (x * A)) ∧ haar (fun x : Matrix κ ι K => φ (x * A)) = ((|Algebra.norm ℚ A.det| : ℚ) : ℂ) ^ Fintype.card κ * haar φ) ∧ ∀ A : Matrix κ κ K, A.det ≠ 0 → IsSB (fun x : Matrix κ ι K => φ (A * x)) ∧ haar (fun x : Matrix κ ι K => φ (A * x)) = ((|Algebra.norm ℚ A.det| : ℚ) : ℂ) ^ Fintype.card ι * haar φ := by sorry
