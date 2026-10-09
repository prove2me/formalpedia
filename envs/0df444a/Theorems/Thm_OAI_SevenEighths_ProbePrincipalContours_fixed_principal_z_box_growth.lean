-- Prove2me | Theorems.Thm_OAI_SevenEighths_ProbePrincipalContours_fixed_principal_z_box_growth
-- name    : OAI.SevenEighths.ProbePrincipalContours.fixed_principal_z_box_growth
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T01:58:20.631134+00:00
-- url     : https://prove2.me/theorems/f01565ab-9311-4d2a-bf57-0b2753629b0e
-- title:
--   Growth of the pole-removed principal L-function on the z box
-- statement:
--   Let $M$ be a nonzero ideal of the Eisenstein integers, $B_z,t\in\mathbb R$ and $\xi\in[33/200,B_z]$. Then $\|\texttt{HeckeOrigin.poleRemoved}\,(\texttt{fixedPrincipal}\,M)\,(6(\xi+it))\|\le\texttt{zBoxAmplitude}\,M\,B_z\cdot\texttt{height}(t)^3$.
--
--   Lean: `OAI.SevenEighths.ProbePrincipalContours.fixed_principal_z_box_growth` in `lean/OAI/NumberTheory/DirichletL/Detector/PrincipalContours.lean` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
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
namespace SevenEighths.ProbePrincipalContours
open HeckeFamily ProbePhysical ProbeEuler ProbeLocal CompletedGauss
open ProbeFiniteProductBounds ProbeFiniteProductX PrincipalMellinResidues
open PrincipalMellinGrowth ProbeMellinBoundary
local notation "Id" => Ideal ActualEisensteinCubic.O

local instance instCountableO_rbd7647_1 : Countable ActualEisensteinCubic.O := ActualEisensteinCubic.latticeCoordEquiv.injective.countable
local instance instCountableIdealO_rbd7647_1 : Countable Id := ConcretePrimeRowBridge.idealGenerator_injective.countable
lemma fixed_principal_z_box_growth (M : Id) [NeZero M] (Bz ξ t : ℝ)
    (hξ : ξ∈Icc (33/200 : ℝ) Bz) :
    ‖HeckeOrigin.poleRemoved (fixedPrincipal M) (6*((ξ:ℂ)+t*I))‖≤zBoxAmplitude M Bz*height t^3 := by
  sorry

end SevenEighths.ProbePrincipalContours
end

end OAI
end
