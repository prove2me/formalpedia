-- Prove2me | Theorems.Thm_GlobalTheory_Sandwich_Model_bound_aux
-- name    : GlobalTheory.Sandwich.Model.bound_aux
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T16:50:02.224722+00:00
-- url     : https://prove2.me/theorems/bd460645-6249-500e-a6aa-962b099b1984
-- title:
--   Model: bound aux
-- statement:
--   The Model construction uses the bound aux property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/MemMixedTsub.lean#L145-L168
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/MemMixedTsub.lean#L145-L168

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

theorem GlobalTheory.Sandwich.Model.bound_aux (X Y : Matrix (Fin h) (Fin h) (Ainf p O)) (hXY : X * Y = mu ε • 1)
    (x : Fin h → O) (hx : Y.map (fontaineTheta O p) *ᵥ x = 0) :
    ∃ y, X.map (fontaineTheta O p) *ᵥ y = fontaineTheta O p (nu ε) • x := by sorry
