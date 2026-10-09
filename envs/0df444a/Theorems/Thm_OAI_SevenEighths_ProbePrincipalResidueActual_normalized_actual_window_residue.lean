-- Prove2me | Theorems.Thm_OAI_SevenEighths_ProbePrincipalResidueActual_normalized_actual_window_residue
-- name    : OAI.SevenEighths.ProbePrincipalResidueActual.normalized_actual_window_residue
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T02:17:12.045052+00:00
-- url     : https://prove2.me/theorems/8d8b9343-6f07-44d0-be2a-c3816a78fd71
-- title:
--   The normalized window residue is close to the principal signal
-- statement:
--   Let $E$ be a finite set of ideals with `SourceExclusions E`, $\eta$ a `Character`, $a\in(7/8,2]$ with `beta` $<a$, and $S$ finite. Then there is $D\ge0$ such that for all real-valued, nonnegative, nonzero Schwartz $W_0,W_1$ supported in $[a_0,b_0]$, $[a_1,b_1]$ ($a_0,a_1>0$), slot sets $T_j$ of prime ideals coprime to $\eta.\mathrm{modulus}$ with norms $\ge P$, weights $W_j\ge0$ at $N(p)/\mathrm{scale}_j$, positive slot masses, reals $P\ge480$ with $1440P^{-7/8}\le1$, $Y$, $Z\ge1$: with $B=$`windowMultiplier η S T W scale` and $N_Z=$`sourceResidueConstant W0 W1 (∏E)`·`Probe.principalScalar S Z (1/6) (slotMass …)`, we have $N_Z\ne0$, the residue integrand $t\mapsto$`fixedPrincipalResidue (∏E)`$^2/6\cdot$`sourceMultiplier W0 W1 (Z^{17/48}) Y Z (η.excludePrimes E _) (a+it) … 1 (1/6)` is integrable, and
--   $$\Big\|\frac{\texttt{sourceResidueIntegral}(\dots,a,Z^{17/48},Y,Z,\texttt{globalClosedCorrection}\,\eta\,E,B)}{N_Z}-\texttt{signal}(\eta.\texttt{excludePrimes}\,E)(\texttt{sourceCorrection}\,\eta\,E)(-11/16)\,Z\Big\|\le D\,Z^{a-11/16}P^{-7/8}.$$
--
--   Lean: `OAI.SevenEighths.ProbePrincipalResidueActual.normalized_actual_window_residue` in `lean/OAI/NumberTheory/DirichletL/Detector/PrincipalResidueActual.lean` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
-- source:
--   OpenAI, The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re s > 7/8, OpenAI Math Release, September 30, 2026, family 003 of https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory/DirichletL

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B022

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
open Complex MeasureTheory
namespace SevenEighths.ProbePrincipalResidueActual
open HeckeFamily PrincipalMellinResidues PrincipalSignalComparison
open ProbeFiniteProductBounds ProbeEuler ProbeLocal HeckeSignal ProbePhysical Continuation
open ActualEisensteinCubic CompletedGauss

theorem normalized_actual_window_residue {κ : Type*}
    (E : Finset (Ideal HeckeFamily.O)) (hE : SourceExclusions E) (η : Character)
    {a : ℝ} (ha : 7/8<a) (ha2 : a≤2) (hβ : HeckeZeroSupremum.beta<a) (S : Finset κ) :
    letI : NeZero (∏p∈E,p) := ⟨fixedPrimeProduct_ne_zero E hE.prime⟩
    ∃D : ℝ, 0≤D ∧ ∀ (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ),
      0<a0 → 0<a1 → Function.support W0⊆Set.Icc a0 b0 →
      Function.support W1⊆Set.Icc a1 b1 →
      (∀y,(W0 y).im=0) → (∀y,(W1 y).im=0) →
      (∀y,0≤(W0 y).re) → (∀y,0≤(W1 y).re) → W0≠0 → W1≠0 →
      ∀ (T : κ → Finset PrimeIdeal) (W : κ → ℝ → ℝ) (scale : κ → ℝ) (P Y Z : ℝ),
      480≤P → 1440*P^(-(7/8 : ℝ))≤1 →
      (∀j∈S,∀p∈T j,0≤W j ((Ideal.absNorm p.val : ℝ)/scale j)) →
      (∀j∈S,∀p∈T j,P≤(Ideal.absNorm p.val : ℝ)) →
      (∀j∈S,∀p∈T j,IsCoprime p.val η.modulus) →
      (∀j∈S,0<slotMass T (residueWeights W scale) j) → 1≤Z →
      let B := windowMultiplier η S T (fun j t => (W j t : ℂ)) scale
      let normer := sourceResidueConstant W0 W1 (∏p∈E,p) *
        (Probe.principalScalar S Z (1/6) (slotMass T (residueWeights W scale)) : ℂ)
      normer≠0 ∧
      Integrable (fun t : ℝ => fixedPrincipalResidue (∏p∈E,p)^2/6 *
        sourceMultiplier W0 W1 (Z^(17/48 : ℝ)) Y Z (η.excludePrimes E hE.prime)
          ((a : ℂ)+t*I) (globalClosedCorrection η E ((a : ℂ)+t*I))
          (B ((a : ℂ)+t*I)) 1 (1/6)) ∧
      ‖sourceResidueIntegral W0 W1 (∏p∈E,p) (η.excludePrimes E hE.prime)
          a (Z^(17/48 : ℝ)) Y Z (globalClosedCorrection η E) B / normer -
          signal (η.excludePrimes E hE.prime) (sourceCorrection η E) (-11/16) Z‖ ≤
        D*Z^(a-11/16)*P^(-(7/8 : ℝ)) := by
  sorry

end SevenEighths.ProbePrincipalResidueActual
end

end OAI
end
