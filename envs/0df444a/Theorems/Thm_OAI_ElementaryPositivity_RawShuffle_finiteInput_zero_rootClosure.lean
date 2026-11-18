-- Prove2me | Theorems.Thm_OAI_ElementaryPositivity_RawShuffle_finiteInput_zero_rootClosure
-- name    : OAI.ElementaryPositivity.RawShuffle.finiteInput_zero_rootClosure
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T18:22:30.246089+00:00
-- url     : https://prove2.me/theorems/0f280d36-9124-44ec-a6aa-239e17ed8068
-- title:
--   OAI.ElementaryPositivity.RawShuffle.finiteInput_zero_rootClosure: intermediate lemma from OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.elementaryPositivityWitness_exists`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Elementary Positivity of Chromatic Quasisymmetric Functions*, OpenAI Math Release, September 24, 2026, result family 169, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ElementaryPositivity.RawShuffle.finiteInput_zero_rootClosure` of [lean/OAI/Combinatorics/Chromatic/Shuffle/PrimitiveRootClosure.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Shuffle/PrimitiveRootClosure.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ElementaryPositivity.RawShuffle`, with `open SlopeArithmetic UnitSelections`, `open QuantumTorus WeightedTorusSeries WallUnits PowerSeries`):
--
--   ```lean
--   theorem finiteInput_zero_rootClosure (ε : I→Bool) (ha : ∀i,a i i=elementaryDiagonal ε i) :
--       InPrecisionClosure LaurentRay.vUnit Ω (literalRootProducts Ω C V)
--         (PowerSeriesSplit.zeroFactor (positiveProject LaurentRay.vUnit Ω h)
--           (zeroProject LaurentRay.vUnit Ω h)
--           (push w LaurentRay.vUnit Ω P (literalInputCoefficient a κ ε)))
--   ```
--
--   **Definitions.** The statement is written with `OAI.ElementaryPositivity.PowerSeriesSplit.zeroFactor`, `OAI.ElementaryPositivity.QuantumTorus.HasRootDegree`, `OAI.ElementaryPositivity.QuantumTorus.Torus`, `OAI.ElementaryPositivity.QuantumTorus.literalRootProducts`, `OAI.ElementaryPositivity.QuantumTorus.positiveProject`, `OAI.ElementaryPositivity.QuantumTorus.zeroProject`, `OAI.ElementaryPositivity.QuantumTorus.Torus.instRing` and `OAI.ElementaryPositivity.WallUnits.LaurentRay.vUnit` (definitions bundle `OAIQ368Chrom001` of this split); `OAI.ElementaryPositivity.QuantumTorus.InPrecisionClosure` (definitions bundle `OAIQ368Chrom013` of this split); `OAI.ElementaryPositivity.RawShuffle.eulerForm` (definitions bundle `OAIQ368Chrom017` of this split); `OAI.ElementaryPositivity.RawShuffle.elementaryDiagonal`, `OAI.ElementaryPositivity.RawShuffle.literalInputCoefficient`, `OAI.ElementaryPositivity.WeightedTorusSeries.push` and `OAI.ElementaryPositivity.WeightedTorusSeries.weight` (definitions bundle `OAIQ368Chrom018` of this split); `OAI.ElementaryPositivity.RawShuffle.slopeValue` (definitions bundle `OAIQ368Chrom021` of this split); `OAI.ElementaryPositivity.RawShuffle.SlopeEulerSymmetric` (definitions bundle `OAIQ368Chrom022` of this split); `OAI.ElementaryPositivity.RawShuffle.slopeDimensions` (definitions bundle `OAIQ368Chrom023` of this split).
--
--   **Used by.** The proof of `OAI.ElementaryPositivity.QuantumTorus.wall_joint_induction` of this split imports it.
-- source:
--   OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 169; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Elementary-Positivity-of-Chromatic-Quasisymmetric-Functions-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Shuffle/PrimitiveRootClosure.lean (declaration OAI.ElementaryPositivity.RawShuffle.finiteInput_zero_rootClosure)

import Mathlib
import Definitions.Def_OAIQ368Chrom013
import Definitions.Def_OAIQ368Chrom023

section

attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open SlopeArithmetic UnitSelections
open QuantumTorus WeightedTorusSeries WallUnits PowerSeries
noncomputable section
variable {I J M : Type*} [Fintype I] [DecidableEq I] [Fintype J] [AddCommGroup M]
variable (a : I→I→ℕ) (κ : I→ℤ) (c η : I→ℝ) (hc : ∀i,0 < c i)
  [hχ : Fact (∀θ,SlopeEulerSymmetric a c η θ)]
local instance instFactSlopeEulerSymmetric_2_r66162f_1 (θ : ℝ) : Fact (SlopeEulerSymmetric a c η θ) := ⟨hχ.out θ⟩
variable (w : I→ℕ) [Fact (∀i,0<w i)]
variable (Ω : M→+M→+ℤ) (P : (I→ℕ)→+M) (C : (J→ℤ)→+M)
variable (hgeom : ∀d e,Ω (P d) (P e)=eulerForm a d e-eulerForm a e d)
variable (hroot : ∀d,HasRootDegree C (WeightedTorusSeries.weight w d) (P d))
variable (θ : ℝ) (V : M→Prop) (hv : ∀d∈slopeDimensions c η hc θ,V (P d))

variable (h : M→+ℝ) (hh : ∀d,h (P d)=slopeValue c η θ d)
include hgeom hroot hv hh in
theorem finiteInput_zero_rootClosure (ε : I→Bool) (ha : ∀i,a i i=elementaryDiagonal ε i) :
    InPrecisionClosure LaurentRay.vUnit Ω (literalRootProducts Ω C V)
      (PowerSeriesSplit.zeroFactor (positiveProject LaurentRay.vUnit Ω h)
        (zeroProject LaurentRay.vUnit Ω h)
        (push w LaurentRay.vUnit Ω P (literalInputCoefficient a κ ε))) := by
  sorry
end
end ElementaryPositivity.RawShuffle

end

end OAI
end
