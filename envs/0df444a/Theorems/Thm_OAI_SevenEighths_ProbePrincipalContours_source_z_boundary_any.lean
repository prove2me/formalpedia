-- Prove2me | Theorems.Thm_OAI_SevenEighths_ProbePrincipalContours_source_z_boundary_any
-- name    : OAI.SevenEighths.ProbePrincipalContours.source_z_boundary_any
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T01:44:15.883531+00:00
-- url     : https://prove2.me/theorems/e975eb1f-95c7-4d40-8ab0-7e0f5c148111
-- title:
--   Boundary control of the source multiplier in z
-- statement:
--   Let $\eta$, $S$ (with `SourceExclusions S`), $J$, $T$, $b$ be as above, $W_0$ Schwartz supported in $[a_0,b_0]$ with $a_0>0$, $W_1$ Schwartz, reals $X,Z>0$, $Y$, $s$ with $\operatorname{Re}s\ge7/8$ and `LFunction (η.excludePrimes S _) s` $\ne0$, and $e>0$. Then the function $z\mapsto$`sourceMultiplier W0 W1 X Y Z (η.excludePrimes S _) s (globalClosedCorrection η S s) (slotMultiplier η J T b s) 1 z`·`LFunction (fixedSourcePrincipal S _) (6z)` satisfies `BoundaryControl` between $33/200$ and $1/6+e$.
--
--   Lean: `OAI.SevenEighths.ProbePrincipalContours.source_z_boundary_any` in `lean/OAI/NumberTheory/DirichletL/Detector/PrincipalContours.lean` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
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

local instance instCountableO_r4a0014_1 : Countable ActualEisensteinCubic.O := ActualEisensteinCubic.latticeCoordEquiv.injective.countable
local instance instCountableIdealO_r4a0014_1 : Countable Id := ConcretePrimeRowBridge.idealGenerator_injective.countable
theorem source_z_boundary_any {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 : ℝ) (ha0 : 0<a0)
    (hW0 : Function.support W0⊆Icc a0 b0) (X Y Z : ℝ) (hX : 0<X) (hZ : 0<Z)
    (s : ℂ) (hs : 7/8≤ s.re) (hη : LFunction (η.excludePrimes S hS.prime) s≠0)
    {e : ℝ} (he : 0<e) :
    BoundaryControl (fun z => sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (slotMultiplier η J T b s) 1 z *
      LFunction (fixedSourcePrincipal S hS.prime) (6*z)) (33/200) (1/6+e) := by
  sorry

end SevenEighths.ProbePrincipalContours
end

end OAI
end
