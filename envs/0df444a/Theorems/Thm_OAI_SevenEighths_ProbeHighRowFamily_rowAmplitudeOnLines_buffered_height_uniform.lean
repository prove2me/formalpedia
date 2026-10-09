-- Prove2me | Theorems.Thm_OAI_SevenEighths_ProbeHighRowFamily_rowAmplitudeOnLines_buffered_height_uniform
-- name    : OAI.SevenEighths.ProbeHighRowFamily.rowAmplitudeOnLines_buffered_height_uniform
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T02:19:37.608977+00:00
-- url     : https://prove2.me/theorems/b4d525ab-5184-415b-b5be-e5e4970c371c
-- title:
--   Height-uniform bound for row amplitudes on the buffered line
-- statement:
--   For $0<e<1/1000$, $S$ maximal with `SourceExclusions S` and `FirstTail (4e) S`, primes outside $S$, $\eta$, $u\ne1$, twists $\psi$ and $r\ge17/50$, there is $C\ge0$ such that for all $a\in[51/100,1]$, $B>2$, $H\le(3i+2)B$ with the detector condition, $\sigma\in[a+16e,2]$ and $|t_{11}|\le H$: $\|\texttt{rowAmplitudeOnLines}(\dots,\sigma,1-a-6e,r,t)\|\le C(3+|H|)^2(3+|t_2|)^2$.
--
--   Lean: `OAI.SevenEighths.ProbeHighRowFamily.rowAmplitudeOnLines_buffered_height_uniform` in `lean/OAI/NumberTheory/DirichletL/PrimeRows/BufferedJoinDecay.lean` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
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

lemma rowAmplitudeOnLines_buffered_height_uniform {K : ℕ}
    (e : ℝ) (he : 0<e) (he' : e<1/1000)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S) (P : Fin K→_root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hPS : ∀i,(P i).val∉S)
    (η : Character) (u : FreeRow) (hu : u.val≠1) (ψ : ι→Character)
    (r : ℝ) (hr : (17/50:ℝ)≤ r) :
    ∃C : ℝ,0≤C ∧ ∀a B H : ℝ,∀i : ℕ,(51/100:ℝ)≤a → a≤1 → 2<B →
      H≤(3*i+2:ℕ)*B → detectorMaximum (sourceDetectorFamily S hS.prime η u ψ) (3*(i+1:ℕ)*B)<a+2*e →
      ∀σ∈Icc (a+16*e) 2,∀t : HeightSpace, |t.1.1|≤H →
      ‖rowAmplitudeOnLines S hS hmax P hPS η u σ (1-a-6*e) r t‖≤C*(3+|H|)^2*(3+|t.2|)^2 := by
  sorry

end SevenEighths.ProbeHighRowFamily

end

end OAI
end
