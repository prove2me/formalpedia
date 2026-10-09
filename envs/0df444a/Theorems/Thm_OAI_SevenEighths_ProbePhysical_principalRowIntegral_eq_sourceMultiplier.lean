-- Prove2me | Theorems.Thm_OAI_SevenEighths_ProbePhysical_principalRowIntegral_eq_sourceMultiplier
-- name    : OAI.SevenEighths.ProbePhysical.principalRowIntegral_eq_sourceMultiplier
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T02:21:05.132391+00:00
-- url     : https://prove2.me/theorems/1daf42c6-5e01-4078-af46-9ebdc1bde224
-- title:
--   The principal row integral as a source multiplier integral
-- statement:
--   For $\eta$, $S$ with `SourceExclusions S`, an injective family $P_i$ of prime ideals outside $S$, Schwartz $W_0,W_1$ and reals $X,Y,Z$:
--   $$\texttt{principalRowIntegral}\,\eta\,S\,(P_{\mathrm{gen}})\,W_0\,W_1\,X\,Y\,Z=(2\pi)^{-3}\int\texttt{sourceMultiplier}(\dots,3+it_{11},\dots,3+it_2,2+it_{12})\,L(\pi,6(2+it_{12}))\,L(\pi,3+it_2)\,d\,\texttt{heightMeasure}(t),$$
--   with $\pi=$`fixedSourcePrincipal S _`, the multiplier built with `globalClosedCorrection` and `slotMultiplier` of the singletons $\{P_i\}$.
--
--   Lean: `OAI.SevenEighths.ProbePhysical.principalRowIntegral_eq_sourceMultiplier` in `lean/OAI/NumberTheory/DirichletL/Detector/PrincipalInput.lean` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
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
open CompletedGauss CanonicalQuadraticSieve ProbeMellinBoundary
open PrincipalMellinResidues ProbeFiniteProductBounds
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

theorem principalRowIntegral_eq_sourceMultiplier {K : ℕ} (η : HeckeFamily.Character)
    (S : Finset Id) (hS : SourceExclusions S) (P : Fin K→PrimeIdeal)
    (hP : Function.Injective P) (hPS : ∀i,(P i).val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) :
    principalRowIntegral η S (fun i=>primaryGenerator (P i).val) W0 W1 X Y Z=
      ((1/(2*Real.pi):ℝ):ℂ)^3*∫t : HeightSpace,
        sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) ((3:ℂ)+t.1.1*Complex.I)
          (globalClosedCorrection η S ((3:ℂ)+t.1.1*Complex.I))
          (slotMultiplier η Finset.univ (fun i=>{P i}) (fun _ _=>1) ((3:ℂ)+t.1.1*Complex.I))
          ((3:ℂ)+t.2*Complex.I) ((2:ℂ)+t.1.2*Complex.I)*
        HeckeFamily.LFunction (fixedSourcePrincipal S hS.prime) (6*((2:ℂ)+t.1.2*Complex.I))*
        HeckeFamily.LFunction (fixedSourcePrincipal S hS.prime) ((3:ℂ)+t.2*Complex.I) ∂heightMeasure := by
  sorry

end SevenEighths.ProbePhysical
end

end OAI
end
