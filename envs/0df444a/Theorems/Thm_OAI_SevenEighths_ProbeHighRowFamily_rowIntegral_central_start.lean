-- Prove2me | Theorems.Thm_OAI_SevenEighths_ProbeHighRowFamily_rowIntegral_central_start
-- name    : OAI.SevenEighths.ProbeHighRowFamily.rowIntegral_central_start
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T02:19:43.722535+00:00
-- url     : https://prove2.me/theorems/a4c18f89-6809-43a9-b7d8-4fd02464bbe4
-- title:
--   Row integral on the starting lines
-- statement:
--   For $a\in[51/100,1]$, $0<e<1/1000$, $S$ maximal with `SourceExclusions S` and `FirstTail (4e) S`, injective primes outside $S$, $\eta$, $u\ne1$, Schwartz $W_0,W_1$ as above and $X,Y,Z>0$: `continuedRowOnLines … 2 (1-a-6e) (17/50)` is integrable for `heightMeasure` and `rowIntegral … u` $=(2\pi)^{-3}\int$ of it.
--
--   Lean: `OAI.SevenEighths.ProbeHighRowFamily.rowIntegral_central_start` in `lean/OAI/NumberTheory/DirichletL/PrimeRows/FirstTransport.lean` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
-- source:
--   OpenAI, The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re s > 7/8, OpenAI Math Release, September 30, 2026, family 003 of https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory/DirichletL

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B027

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O

theorem rowIntegral_central_start {K : ℕ}
    (a e : ℝ) (ha : (51/100:ℝ)≤a) (ha1 : a≤1) (he : 0<e) (he' : e<1/1000)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S) (P : Fin K→_root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hP : Function.Injective P)
    (hPS : ∀i,(P i).val∉S) (η : Character) (u : FreeRow) (hu : u.val≠1)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z) :
    Integrable (continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z 2 (1-a-6*e) (17/50)) heightMeasure ∧
    rowIntegral η S (calibrationForSet S hmax)
      (fun i=>CompletedGauss.primaryGenerator (P i).val) W0 W1 X Y Z u=
      ((1/(2*Real.pi):ℝ):ℂ)^3*
        ∫p : HeightSpace,continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z 2 (1-a-6*e) (17/50) p ∂heightMeasure := by
  sorry

end SevenEighths.ProbeHighRowFamily

end

end OAI
end
