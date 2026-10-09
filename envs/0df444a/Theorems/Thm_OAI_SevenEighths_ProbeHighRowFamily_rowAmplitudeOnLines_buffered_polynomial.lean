-- Prove2me | Theorems.Thm_OAI_SevenEighths_ProbeHighRowFamily_rowAmplitudeOnLines_buffered_polynomial
-- name    : OAI.SevenEighths.ProbeHighRowFamily.rowAmplitudeOnLines_buffered_polynomial
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T02:19:14.909879+00:00
-- url     : https://prove2.me/theorems/bfcfea2f-d366-43b5-b713-f331a8b773c1
-- title:
--   Row amplitudes on the buffered line, uniform in the row
-- statement:
--   For $K$, $0<e<1/1000$ and $S$ maximal with `SourceExclusions S` and `FirstTail (4e) S`, there is $C\ge0$ such that for every $\eta$, $u\ne1$, injective primes $P$ outside $S$, twists, $a,B,H,i$ with the detector condition, $\sigma\in[a+16e,2]$, $r\in[17/50,1]$ and $|t_{11}|\le H$: $\|\texttt{rowAmplitudeOnLines}(\dots)\|\le C\,\texttt{contourArithmeticCost}\,\eta\,u\,P\,(3+|H|)^2(3+|t_2|)^2$.
--
--   Lean: `OAI.SevenEighths.ProbeHighRowFamily.rowAmplitudeOnLines_buffered_polynomial` in `lean/OAI/NumberTheory/DirichletL/PrimeRows/CoarseAmplitude.lean` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
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

theorem rowAmplitudeOnLines_buffered_polynomial (K : ℕ)
    (e : ℝ) (he : 0<e) (he' : e<1/1000)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (4*e) S)
    (hmax : ∀P∈S,P.IsMaximal) :
    ∃C : ℝ,0≤C ∧ ∀(η : Character) (u : FreeRow),u.val≠1 →
      ∀(P : Fin K→_root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal),Function.Injective P → ∀hPS : ∀j,(P j).val∉S,
      ∀ψ : ι→Character,∀a B H : ℝ,∀i : ℕ,(51/100:ℝ)≤a → a≤1 → 2<B → H≤(3*i+2:ℕ)*B →
      detectorMaximum (sourceDetectorFamily S hS.prime η u ψ) (3*(i+1:ℕ)*B)<a+2*e →
      ∀σ∈Icc (a+16*e) 2,∀r∈Icc (17/50:ℝ) 1,∀t : HeightSpace,|t.1.1|≤H →
      ‖rowAmplitudeOnLines S hS hmax P hPS η u σ (1-a-6*e) r t‖≤
        C*contourArithmeticCost η u P*(3+|H|)^2*(3+|t.2|)^2 := by
  sorry

end SevenEighths.ProbeHighRowFamily

end

end OAI
end
