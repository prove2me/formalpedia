-- Prove2me | Theorems.Thm_GlobalTheory_SW_EisConv_span_rows_mul
-- name    : GlobalTheory.SW.EisConv.span_rows_mul
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T00:26:29.000807+00:00
-- url     : https://prove2.me/theorems/eaf473b5-4ce6-453d-b854-f6999fbabfcc
-- title:
--   Eis Conv: span rows mul
-- statement:
--   The Eis Conv construction uses the span rows mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/SummableEisMajorant.lean#L115-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/SummableEisMajorant.lean#L115-L129

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_UnitaryActHalfSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_PosSemidefSubMulConjTranspose
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsLinearIndependentOfRatIndependent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SummableEisMajorant
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.EisConv
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {N : ℕ}
omit [NumberField E] [IsCMField E]

theorem GlobalTheory.SW.EisConv.span_rows_mul {m : Type} (a : Matrix (Fin N) (Fin N) E) (ha : a.det ≠ 0)
    (W : Matrix (Fin N) m E) :
    Submodule.span E (Set.range fun i => (a * W) i) = Submodule.span E (Set.range fun i => W i) := by sorry
