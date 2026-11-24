-- Prove2me | Theorems.Thm_GlobalTheory_ClassSumCompare_mem_hat_of_mem
-- name    : GlobalTheory.ClassSumCompare.mem_hat_of_mem
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T13:26:56.972388+00:00
-- url     : https://prove2.me/theorems/25fc590c-5a5c-445c-82ee-5efdd3197f1a
-- title:
--   Class Sum Compare: mem hat of mem
-- statement:
--   The Class Sum Compare construction uses the mem hat of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsNatMulInt.lean#L27-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsNatMulInt.lean#L27-L43

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_AdelicNormWeight
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FiniteAdeleStrongApproximationModNat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionFractionalIdealProperties
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsNatMulInt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.ClassSumCompare
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField IsDedekindDomain GlobalTheory.IndefiniteRowSideFullHecke.AdelicNormWeight
open scoped TensorProduct nonZeroDivisors
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem GlobalTheory.ClassSumCompare.mem_hat_of_mem {x : AdE E} (hx : x ∈ intAd E) :
    (show GlobalTheory.AdLat.RA (maximalRealSubfield E) E from x) ∈
      GlobalTheory.AdLat.hat1 (maximalRealSubfield E) ((1 : FractionalIdeal (𝓞 E)⁰ E) : Set E) := by sorry
