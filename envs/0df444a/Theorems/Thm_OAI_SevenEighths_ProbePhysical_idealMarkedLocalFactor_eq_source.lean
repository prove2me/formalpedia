-- Prove2me | Theorems.Thm_OAI_SevenEighths_ProbePhysical_idealMarkedLocalFactor_eq_source
-- name    : OAI.SevenEighths.ProbePhysical.idealMarkedLocalFactor_eq_source
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T02:19:21.142725+00:00
-- url     : https://prove2.me/theorems/f1e3606d-3790-4913-9134-89a95658b57d
-- title:
--   The marked local factor is the principal marked series
-- statement:
--   For a `Supported` prime ideal $P$ with primary generator $p$ and all $x,w,z$: `idealMarkedLocalFactor η P x w z` $=$ `principalMarkedSeries p … (targetMonoid η p) (actualACube η p) (N(P)^{-x}) (N(P)^{-w}) (coordV (N P) z)`.
--
--   Lean: `OAI.SevenEighths.ProbePhysical.idealMarkedLocalFactor_eq_source` in `lean/OAI/NumberTheory/DirichletL/Detector/MarkedLocal.lean` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
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
open ActualEisensteinCubic CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss ProbeEuler ProbeRow ConcretePrimeRowBridge
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma idealMarkedLocalFactor_eq_source (η : HeckeFamily.Character) (P : PrimeIdeal)
    (hs : Supported P.val) (x w z : ℂ) :
    let p := primaryGenerator P.val
    let hp := supported_primeGenerator_prime P hs
    letI : (Ideal.span {p}:Id).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
    let hg := (supported_prime_data p hp ((span_primaryGenerator_of_supported P.val hs).symm ▸ hs)).1
    idealMarkedLocalFactor η P x w z=
      principalMarkedSeries p hp hg (targetMonoid η p) (actualACube η p)
        ((Ideal.absNorm P.val:ℂ)^(-x)) ((Ideal.absNorm P.val:ℂ)^(-w))
        (coordV (Ideal.absNorm P.val) z) := by
  sorry

end SevenEighths.ProbePhysical
end

end OAI
end
