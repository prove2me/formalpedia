-- Prove2me | Theorems.Thm_OAI_SevenEighths_ProbePhysical_idealHighLocalFactor_eq_source
-- name    : OAI.SevenEighths.ProbePhysical.idealHighLocalFactor_eq_source
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T02:22:55.570276+00:00
-- url     : https://prove2.me/theorems/2e609d4d-e0ad-46c2-ad4a-93c2e1b8f43d
-- title:
--   The high local factor at a prime is the source principal series
-- statement:
--   Let $p$ be a prime Eisenstein integer with $(p)$ maximal, avoiding `goodLambda`, of odd residue characteristic, $p\equiv1\bmod$ `goodLambda`$^2$ and `Supported`. Then `idealHighLocalFactor η (p) x w z` $=$ `sourcePrincipalSeries p hp hg (targetMonoid η p) (actualACube η p) x w z` for all $x,w,z$.
--
--   Lean: `OAI.SevenEighths.ProbePhysical.idealHighLocalFactor_eq_source` in `lean/OAI/NumberTheory/DirichletL/Detector/IdealLocalEuler.lean` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
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
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion CanonicalQuadraticSieve
open ConcretePrimeRowBridge CubicEisenstein ProbePhase ProbeEuler ProbePrimePower ProbeRow
local notation "O" => ActualEisensteinCubic.O

theorem idealHighLocalFactor_eq_source (η : HeckeFamily.Character) (p : O) (hp : Prime p)
    [(Ideal.span {p}:Ideal O).IsMaximal] (hg : goodLambda∉Ideal.span {p})
    (hchar : ringChar (O ⧸ Ideal.span {p})≠2) (hprimary : goodLambda^2∣p-1)
    (hs : Supported (Ideal.span {p})) (x w z : ℂ) :
    idealHighLocalFactor η (Ideal.span {p}) x w z =
      sourcePrincipalSeries p hp hg (targetMonoid η p) (actualACube η p) x w z := by
  sorry

end SevenEighths.ProbePhysical
end

end OAI
end
