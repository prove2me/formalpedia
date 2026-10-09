-- Prove2me | Theorems.Thm_OAI_SevenEighths_ProbePhysical_source_principalHigh_L_factorization
-- name    : OAI.SevenEighths.ProbePhysical.source_principalHigh_L_factorization
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T02:19:55.020743+00:00
-- url     : https://prove2.me/theorems/65eb81b6-c38b-449b-ad1a-c043e77c0573
-- title:
--   The principal high series as a quotient of L-functions
-- statement:
--   For $S$ with `SourceExclusions S`, $\eta$ and $x,w,z$ with $\operatorname{Re}x>3/2$, $\operatorname{Re}w>2$, $\operatorname{Re}z>1/6$:
--   $$\texttt{markedIdealHighSeries}\,S\,1\,\eta\,1\,x\,w\,z=\frac{L(\pi,6z)\,L(\pi,w)}{L(\eta_S,x)}\cdot\texttt{globalClosedCorrection}\,\eta\,S\,x\,w\,z,$$
--   $\pi=$`fixedSourcePrincipal S _`, $\eta_S=$`η.excludePrimes S _`.
--
--   Lean: `OAI.SevenEighths.ProbePhysical.source_principalHigh_L_factorization` in `lean/OAI/NumberTheory/DirichletL/Detector/SourceExclusions.lean` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
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
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CanonicalQuadraticSieve UniqueFactorizationMonoid ProbeEuler
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

theorem source_principalHigh_L_factorization (S : Finset Id) (hS : SourceExclusions S)
    (η : HeckeFamily.Character) (x w z : ℂ) (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    markedIdealHighSeries S 1 η 1 x w z =
      HeckeFamily.LFunction (fixedSourcePrincipal S hS.prime) (6*z) *
      HeckeFamily.LFunction (fixedSourcePrincipal S hS.prime) w /
        HeckeFamily.LFunction (η.excludePrimes S hS.prime) x * globalClosedCorrection η S x w z := by
  sorry

end SevenEighths.ProbePhysical
end

end OAI
end
