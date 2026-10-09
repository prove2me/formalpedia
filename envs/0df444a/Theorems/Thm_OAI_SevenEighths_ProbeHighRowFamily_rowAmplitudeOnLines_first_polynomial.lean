-- Prove2me | Theorems.Thm_OAI_SevenEighths_ProbeHighRowFamily_rowAmplitudeOnLines_first_polynomial
-- name    : OAI.SevenEighths.ProbeHighRowFamily.rowAmplitudeOnLines_first_polynomial
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T02:20:38.719968+00:00
-- url     : https://prove2.me/theorems/c02fa791-8a5b-461c-a508-7c1193578e6f
-- title:
--   Row amplitudes on the first line, uniform in the row
-- statement:
--   For $K$ and $S$ maximal with `SourceExclusions S` and `FirstTail (1/4) S`, there is $C\ge0$ such that for every $\eta$, $u\ne1$, injective primes $P$ outside $S$, $\upsilon\ge-1/100$, $r\in[17/50,1]$ and $t$: $\|\texttt{rowAmplitudeOnLines}(\dots,2,\upsilon,r,t)\|\le C\,\texttt{contourArithmeticCost}\,\eta\,u\,P\,(3+|t_2|)^2$.
--
--   Lean: `OAI.SevenEighths.ProbeHighRowFamily.rowAmplitudeOnLines_first_polynomial` in `lean/OAI/NumberTheory/DirichletL/PrimeRows/CoarseAmplitude.lean` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
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

theorem rowAmplitudeOnLines_first_polynomial (K : ℕ)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (1/4) S)
    (hmax : ∀P∈S,P.IsMaximal) :
    ∃C : ℝ,0≤C ∧ ∀(η : Character) (u : FreeRow),u.val≠1 →
      ∀(P : Fin K→_root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal),Function.Injective P → ∀hPS : ∀j,(P j).val∉S,
      ∀υ : ℝ,-(1/100:ℝ)≤υ → ∀r∈Icc (17/50:ℝ) 1,∀t : HeightSpace,
      ‖rowAmplitudeOnLines S hS hmax P hPS η u 2 υ r t‖≤
        C*contourArithmeticCost η u P*(3+|t.2|)^2 := by
  sorry

end SevenEighths.ProbeHighRowFamily

end

end OAI
end
