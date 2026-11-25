-- Prove2me | Theorems.Thm_GlobalTheory_Sandwich_Model_smul_Fil_le
-- name    : GlobalTheory.Sandwich.Model.smul_Fil_le
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T16:50:33.422394+00:00
-- url     : https://prove2.me/theorems/f7701439-0f60-4df1-9afb-6eb02a3f6374
-- title:
--   Model: smul Fil le
-- statement:
--   The Model construction uses the smul Fil le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/MemMixedTsub.lean#L170-L172
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/MemMixedTsub.lean#L170-L172

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_XiMulNu
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ValuationCoeEqNorm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_MemMixedTsub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open WittVector Ideal Matrix
open GlobalTheory GlobalTheory.Sandwich GlobalTheory.Sandwich.Model
variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (span {(p : O)}) O]
variable {C : Type} [Field C] [IsAlgClosed C] [CharZero C] {v : Valuation C NNReal} [Algebra O C]
  (hv : v.Integers O) {ε : PreTilt O p}
  (hε : IsPrimitiveRoot (((frobeniusEquiv (PreTilt O p) p).symm ε).untilt) p)
include hv hε
variable {h : ℕ} {Λ : Type} [CommRing Λ] [Algebra ℤ_[p] Λ] (D : Datum ε h Λ)

theorem GlobalTheory.Sandwich.Model.smul_Fil_le (x : Fin h → O) (hx : x ∈ D.Fil) :
    fontaineTheta O p (nu ε) • x ∈ LinearMap.range D.al := by sorry
