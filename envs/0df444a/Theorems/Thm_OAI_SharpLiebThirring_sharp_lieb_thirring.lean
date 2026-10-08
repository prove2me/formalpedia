-- Prove2me | Theorems.Thm_OAI_SharpLiebThirring_sharp_lieb_thirring
-- name    : OAI.SharpLiebThirring.sharp_lieb_thirring
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:33:20.086022+00:00
-- url     : https://prove2.me/theorems/fe8cd2c8-ae04-4d72-a69d-e53781c104dc
-- statement:
--   The theorem states that the full sharp Lieb–Thirring claim MainClaim holds. Here the form domain is H¹(ℝ;ℂ), given as an L² function with an L² weak derivative; for a real potential W, a weak eigenfunction at negative energy −k² (k>0) is u in H¹ with ∫ conj(v′)u′ − ∫ W conj(v)u = −k² ∫ conj(v)u for every v in H¹. negativeMoment(γ,W) is the supremum, in [0,∞], over all finite L²-orthonormal families of such eigenfunctions with parameters k_i of the sum of (k_i)^(2γ), so it is the sum over negative eigenvalues with multiplicity and is not assumed finite. oneStateMoment keeps a single eigenfunction. A potential W is Admissible for γ if W ≥ 0 almost everywhere and W lies in L^(γ+1/2); potentialMass(γ,W) = ∫ W^(γ+1/2). The semiclassical constant is Γ(γ+1)/(2√π Γ(γ+3/2)) and the sharp constant is 2((γ−1/2)/(γ+1/2))^(γ−1/2) times it. optimalConstant and oneStateConstant are the suprema of negativeMoment/potentialMass and oneStateMoment/potentialMass over admissible W with positive mass. The equality potential is, with r=(γ−1/2)⁻¹, (r+1)·sech²(r x). The claim says: for every γ with 1/2<γ<3/2, (1) every admissible W satisfies negativeMoment(γ,W) ≤ sharpConstant(γ)·potentialMass(γ,W); (2) optimalConstant(γ) equals the sharp constant; (3) oneStateConstant(γ) also equals the sharp constant; (4) the equality potential is admissible with positive mass; and (5) for it, negativeMoment equals the sharp constant times its potential mass. No finite spectral cutoff is imposed.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/LiebThirring.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/LiebThirring.lean; bytes 3754..3950
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_LiebThirring

namespace OAI

noncomputable section

open MeasureTheory

open scoped ENNReal Matrix.Norms.L2Operator

open Matrix

namespace SharpLiebThirring

/-- Full sharp Lieb–Thirring bound, both optimal constants, and equality at the
explicit potential; no finite spectral cutoff is imposed. -/
theorem sharp_lieb_thirring : MainClaim := by
  sorry

end SharpLiebThirring
end
end OAI
