-- Prove2me | Theorems.Thm_OAI_SevenEighths_ProbePrincipalContours_continued_residue_pair_integrable
-- name    : OAI.SevenEighths.ProbePrincipalContours.continued_residue_pair_integrable
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T01:43:46.444084+00:00
-- url     : https://prove2.me/theorems/8f959a63-c505-4bc4-bfa6-173ce891796a
-- title:
--   Integrability of the residue-pair integrand
-- statement:
--   Let $\eta$ be a `Character`, $S$ a finite set of ideals with `SourceExclusions S`, $J$ a finite index set with finite sets $T_j$ of prime ideals outside $S$ and coefficients $b$, $W_0,W_1$ Schwartz functions supported in $[a_0,b_0]$, $[a_1,b_1]$ with $a_0,a_1>0$, and reals $X,Z>0$, $Y$, $a\ge7/8$ with `HeckeZeroSupremum.beta` $<a$, $\xi\ge33/200$ with $6\xi\ne1$. Then the function $(q_1,q_2)\mapsto$`continuedSourceMultiplier η S _ J T b W0 W1 X Y Z (a+iq₁) 1 (ξ+iq₂)`·`LFunction (fixedSourcePrincipal S _) (6(ξ+iq₂))` is integrable on $\mathbb R^2$.
--
--   Lean: `OAI.SevenEighths.ProbePrincipalContours.continued_residue_pair_integrable` in `lean/OAI/NumberTheory/DirichletL/Detector/PrincipalContours.lean` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
-- source:
--   OpenAI, The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re s > 7/8, OpenAI Math Release, September 30, 2026, family 003 of https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory/DirichletL

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B017

section

namespace OAI

noncomputable section

open scoped Classical BigOperators Topology
open Complex Set MeasureTheory Filter
namespace SevenEighths.ProbePrincipalContours
open HeckeFamily ProbePhysical ProbeEuler ProbeLocal CompletedGauss
open ProbeFiniteProductBounds ProbeFiniteProductX PrincipalMellinResidues
open ProbeMellinBoundary
local notation "Id" => Ideal ActualEisensteinCubic.O

local instance instCountableO_r824bfc_1 : Countable ActualEisensteinCubic.O := ActualEisensteinCubic.latticeCoordEquiv.injective.countable
local instance instCountableIdealO_r824bfc_1 : Countable Id := ConcretePrimeRowBridge.idealGenerator_injective.countable
theorem continued_residue_pair_integrable {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z a ξ : ℝ) (hX : 0<X) (hZ : 0<Z)
    (ha : 7/8≤a) (hβ : HeckeZeroSupremum.beta<a) (hξ : 33/200≤ξ) (hξ1 : 6*ξ≠1) :
    Integrable (fun q : ℝ×ℝ => continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z
      ((a:ℂ)+q.1*I) 1 ((ξ:ℂ)+q.2*I)*
        LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+q.2*I))) (volume.prod volume) := by
  sorry

end SevenEighths.ProbePrincipalContours
end

end OAI
end
