-- Prove2me | Theorems.Thm_OAI_SevenEighths_ProbeHighRowFamily_rowIntegral_w_shift
-- name    : OAI.SevenEighths.ProbeHighRowFamily.rowIntegral_w_shift
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T02:19:28.99298+00:00
-- url     : https://prove2.me/theorems/4bdce7e9-3680-42c6-85dd-d8d5b69bda23
-- title:
--   Row integral after shifting the w line
-- statement:
--   For $0<\epsilon\le5/2$, $S$ maximal with `SourceExclusions S` and `FirstTail (ε/2) S`, injective primes outside $S$, $\eta$, $u\ne1$, Schwartz $W_0,W_1$ as above, $X,Y,Z>0$ and $l\in[1/2,3]$: `shiftedRowInner … l` is integrable on $\mathbb R^2$ and `rowIntegral … u` $=(2\pi)^{-3}\int$`shiftedRowInner … l`.
--
--   Lean: `OAI.SevenEighths.ProbeHighRowFamily.rowIntegral_w_shift` in `lean/OAI/NumberTheory/DirichletL/PrimeRows/IteratedShift.lean` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
-- source:
--   OpenAI, The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re s > 7/8, OpenAI Math Release, September 30, 2026, family 003 of https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory/DirichletL

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B027

section

namespace OAI

noncomputable section
open scoped Classical
open MeasureTheory Set Complex
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O

local instance instCountableO_solutions_r4b5f60_1 : Countable O := ActualEisensteinCubic.latticeCoordEquiv.injective.countable
attribute [local instance] OAI.SevenEighths.ProbeHighRowFamily.instMeasurableSpaceFreeRow
local instance instMeasurableSingletonClassFreeRow_r4b5f60_1 : MeasurableSingletonClass FreeRow := ⟨fun _=>trivial⟩
theorem rowIntegral_w_shift {K : ℕ}
    (eps : ℝ) (heps : 0<eps) (heps' : eps≤5/2)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (eps/2) S)
    (hmax : ∀P∈S,P.IsMaximal) (P : Fin K→_root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hP : Function.Injective P)
    (hPS : ∀i,(P i).val∉S) (η : Character) (u : FreeRow) (hu : u.val≠1)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z) (l : ℝ) (hl : (1/2:ℝ)≤l) (hl3 : l≤3) :
    Integrable (shiftedRowInner S hS hmax P hPS η u W0 W1 X Y Z l) (volume.prod volume) ∧
    rowIntegral η S (calibrationForSet S hmax)
      (fun i=>CompletedGauss.primaryGenerator (P i).val) W0 W1 X Y Z u=
      ((1/(2*Real.pi):ℝ):ℂ)^3*
        ∫q : ℝ×ℝ,shiftedRowInner S hS hmax P hPS η u W0 W1 X Y Z l q ∂(volume.prod volume) := by
  sorry

end SevenEighths.ProbeHighRowFamily

end

end OAI
end
