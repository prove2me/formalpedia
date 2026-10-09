-- Prove2me | Theorems.Thm_OAI_SevenEighths_ProbeHighRowFamily_uniform_original_row_central_error
-- name    : OAI.SevenEighths.ProbeHighRowFamily.uniform_original_row_central_error
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T02:19:05.309583+00:00
-- url     : https://prove2.me/theorems/e46bee07-c9cd-4c04-a998-dfe13589d0b9
-- title:
--   Row integral minus its central part is small
-- statement:
--   For $K$, $0<e<1/1000$, $S$ maximal with `SourceExclusions S` and `FirstTail (4e) S`, Schwartz $W_0,W_1$ as above and $N\in\mathbb N$, there is $C\ge0$ such that for every $\eta$, $u\ne1$, injective primes outside $S$, twists, $X,Y>0$, $Z\ge1$, $a\in[51/100,1]$, $B>2$, $0\le H\le(3i+2)B$ with the detector condition:
--   $$\|\texttt{rowIntegral}(\dots,u)-\texttt{centralRowIntegral}(\dots,a,e,H)\|\le C\,\texttt{contourArithmeticCost}\,\eta\,u\,P\,\frac{X^{1/2-17/50}Z^{2+17/50-1}Y^{(1-a-6e)-1}}{\texttt{height}(H)^N}.$$
--
--   Lean: `OAI.SevenEighths.ProbeHighRowFamily.uniform_original_row_central_error` in `lean/OAI/NumberTheory/DirichletL/PrimeRows/UniformError.lean` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
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
variable {ι : Type*} [Fintype ι]

theorem uniform_original_row_central_error (K : ℕ)
    (e : ℝ) (he : 0<e) (he' : e<1/1000)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (N : ℕ) :
    ∃C : ℝ,0≤C ∧ ∀(η : Character) (u : FreeRow),u.val≠1 →
      ∀(P : Fin K→_root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal),Function.Injective P → ∀hPS : ∀j,(P j).val∉S,
      ∀ψ : ι→Character,∀X Y Z : ℝ,0<X → 0<Y → 1≤Z → ∀a B H : ℝ,∀i : ℕ,
      (51/100:ℝ)≤a → a≤1 → 2<B → 0≤H → H≤(3*i+2:ℕ)*B →
      detectorMaximum (sourceDetectorFamily S hS.prime η u ψ) (3*(i+1:ℕ)*B)<a+2*e →
      ‖rowIntegral η S (calibrationForSet S hmax) (fun j=>CompletedGauss.primaryGenerator (P j).val) W0 W1 X Y Z u-
        centralRowIntegral S hS hmax P hPS η u W0 W1 X Y Z a e H‖≤
        C*contourArithmeticCost η u P*(X^(1/2-(17/50:ℝ))*Z^(2+(17/50:ℝ)-1)*Y^((1-a-6*e)-1))/height H^N := by
  sorry

end SevenEighths.ProbeHighRowFamily

end

end OAI
end
