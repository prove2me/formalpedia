-- Prove2me | Theorems.Thm_OAI_SevenEighths_ProbePrincipalRemainderBounds_residue_sharp_pointwise
-- name    : OAI.SevenEighths.ProbePrincipalRemainderBounds.residue_sharp_pointwise
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T01:51:45.246953+00:00
-- url     : https://prove2.me/theorems/608eb95f-6276-489c-99bb-faef05d61a67
-- title:
--   Sharp pointwise bound for the residue-pair integrand
-- statement:
--   With the same data as the full pointwise bound and $6\xi\ne1$, for every $q\in\mathbb R^2$ the norm of the continued source multiplier at $(a+iq_1,1,\xi+iq_2)$ times `LFunction (fixedSourcePrincipal S _) (6(ξ+iq₂))` is at most
--   $$C\,\texttt{slotConstant}\,J\,c\,d\,B\,\xi\cdot\frac{\texttt{zBoxAmplitude}(\prod S)\,1}{|6\xi-1|}\cdot\texttt{scalePower}\,X\,Y\,Z\,a\,\xi\,1\prod_jP_j^{\xi}\cdot\texttt{jointHeight}(q_1,q_2,0)^5\|\texttt{onLines}\,W_0\,W_1\,a\,\xi\,1\,((q_1,q_2),0)\|.$$
--
--   Lean: `OAI.SevenEighths.ProbePrincipalRemainderBounds.residue_sharp_pointwise` in `lean/OAI/NumberTheory/DirichletL/Detector/PrincipalRemainderBounds.lean` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
-- source:
--   OpenAI, The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re s > 7/8, OpenAI Math Release, September 30, 2026, family 003 of https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory/DirichletL

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B019

section

namespace OAI

noncomputable section

open scoped Classical BigOperators Topology
open Complex Set MeasureTheory Filter
namespace SevenEighths.ProbePrincipalRemainderBounds
open HeckeFamily ProbePhysical ProbeEuler ProbeLocal CompletedGauss
open ProbeFiniteProductBounds ProbeFiniteProductX PrincipalMellinResidues
open PrincipalMellinGrowth ProbeMellinBoundary ProbePrincipalContours
local notation "Id" => Ideal ActualEisensteinCubic.O

section Pointwise
variable {ι : Type*} (η : Character) (S : Finset Id) (hS : SourceExclusions S)
  (J : Finset ι) (c d B ξ : ℝ) (hc : 0<c) (hd : c≤d) (hB : 0≤B) (hξ : ξ≤1)
  (W : ι→ℝ→ℝ) (hW : ∀j∈J,∀x,0≤W j x ∧ W j x≤B)
  (hsupp : ∀j∈J,Function.support (W j)⊆Icc c d)
  (P : ι→ℝ) (hP : ∀j∈J,0<P j) (hthreshold : ∀j∈J,480≤ c*P j)
  (hmod : ∀j∈J,(Ideal.absNorm η.modulus:ℝ)<c*P j) (T : ι→Finset PrimeIdeal)
  (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z a υ C : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z)
  (ha : 7/8≤a) (hυ : 19/20≤υ) (hzlo : 33/200≤ξ) (hC : 0≤C)
  (hR : ∀s : ℂ,a≤ s.re→‖HeckeReciprocal.reciprocal (η.excludePrimes S hS.prime) s‖≤C*(1+|s.im|^2))

include hc hd hB hξ hW hsupp hP hthreshold hmod hX hY hZ ha hυ hzlo hC hR

omit hυ in
lemma residue_sharp_pointwise (hξ1 : 6*ξ≠1) (q : ℝ×ℝ) :
    ‖continuedSourceMultiplier η S hS.prime J T
      (fun j p=>(W j ((Ideal.absNorm p.val:ℝ)/P j):ℂ)) W0 W1 X Y Z
      ((a:ℂ)+q.1*I) 1 ((ξ:ℂ)+q.2*I)*
      LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+q.2*I))‖ ≤
    (C*slotConstant J c d B ξ*(zBoxAmplitude (∏p∈S,p) 1/|6*ξ-1|)) *
      (scalePower X Y Z a ξ 1*(∏j∈J,(P j)^ξ))*
      (jointHeight q.1 q.2 0^5*‖onLines W0 W1 a ξ 1 ((q.1,q.2),0)‖) := by
  sorry
end Pointwise

end SevenEighths.ProbePrincipalRemainderBounds

end

end OAI
end
