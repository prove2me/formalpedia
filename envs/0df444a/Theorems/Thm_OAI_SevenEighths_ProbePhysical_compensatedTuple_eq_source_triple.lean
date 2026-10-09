-- Prove2me | Theorems.Thm_OAI_SevenEighths_ProbePhysical_compensatedTuple_eq_source_triple
-- name    : OAI.SevenEighths.ProbePhysical.compensatedTuple_eq_source_triple
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T02:20:10.689013+00:00
-- url     : https://prove2.me/theorems/c6f71895-2a94-4e63-8f0d-34795fc0acef
-- title:
--   Compensated tuples equal the source triple integral
-- statement:
--   For $\eta$, a nonempty finite set $S$ of maximal prime ideals containing `fixedBadPrimes`, Schwartz $W_0,W_1$ supported in $[a_0,b_0]$, $[a_1,b_1]$ ($a_0,a_1>0$), nonzero $p_i$ and $X,Y,Z>0$: `compensatedTuple η (calibrationForSet S hS) W0 W1 p X Y Z` $=$ `tupleSourceTripleIntegral η S (calibrationForSet S hS) W0 W1 p X Y Z`.
--
--   Lean: `OAI.SevenEighths.ProbePhysical.compensatedTuple_eq_source_triple` in `lean/OAI/NumberTheory/DirichletL/Detector/TupleMellin.lean` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
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
open MeasureTheory
namespace SevenEighths.ProbePhysical
open ProbeMellinBoundary CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

theorem compensatedTuple_eq_source_triple {K : ℕ} (η : HeckeFamily.Character)
    (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (hpS : ∀P∈S,Prime P)
    (hbad : fixedBadPrimes⊆S) (hSne : S.Nonempty) (W0 W1 : SchwartzMap ℝ ℂ)
    (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (p : Fin K→O) (hp : ∀i,p i≠0)
    (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z) :
    compensatedTuple η (calibrationForSet S hS) W0 W1 p X Y Z=
      tupleSourceTripleIntegral η S (calibrationForSet S hS) W0 W1 p X Y Z := by
  sorry

end SevenEighths.ProbePhysical
end

end OAI
end
