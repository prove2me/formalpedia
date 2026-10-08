-- Prove2me | Theorems.Thm_OAI_ThorpResults_remaining_main
-- name    : OAI.ThorpResults.remaining_main
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:33:30.632757+00:00
-- url     : https://prove2.me/theorems/df822489-6ee9-4c68-8a27-bb1071948684
-- statement:
--   The theorem states that eight asymptotic results about the Thorp shuffle of 2^d cards, whose positions are the d-bit strings, hold simultaneously. One Thorp step on d≥1 bits uses one fair coin for each (d−1)-bit suffix: the first bit of a position is flipped according to the coin of its remaining bits, and then the bits are cyclically rotated; the d=0 step is the identity. A shuffle of t steps composes t independent such steps, and 'distance' is total variation (half the L¹ distance) from the uniform law on permutations. (1) FrameMain: for every ε>0, for all large d and every starting permutation, the law after 32800·d steps is within total variation ε of uniform. (2) InformationMain has three parts. For large d, any k with 8k≤7·2^d, any start and any list of k distinct labelled positions, the law of the images of the labels after 256·d steps is within ε of uniform on injective k-lists. For large d and 16k≤15·2^d, the same list distance after 1024·d steps is at most (2^d)^(−3/2). Finally, distance(d, 2048·d) tends to 0, and for every d the distance from any start equals distance(d, 2048·d). (3) SpectrumMain: there is p>0 such that for all d≥1 the regularTrace at exponent 2p is at most 17/16 (a sum over Young-diagram shapes of size 2^d of dimension times the trace of |Q|^{2p}, where Q is the averaged Specht-module operator of d-step shuffles) and, for every integer M≥p and every σ, the sweep distance after M·d steps (total variation of the shifted law from uniform) is at most 1/8. (4) SignedMain: for all real η,κ with η>0 there is r≥1 such that, for all d≥1, every shape μ of size 2^d and all Young diagrams α,β,γ with |α|+|β|+|γ|=2^d, the logarithm of the weighted moment dim·Re tr((Q*Q)^r) is at most a(η,d)·signedEntropy(α,β)+remainderBudget(κ,d,|γ|), where a(η,d)=η(1−1/(2√d)), signedEntropy sums log((|α|+|β|)/rowlength) over cells of α and β, and the remainder is 0 if |γ|=0 and otherwise max(0, a(κ,d)·|γ|·log 2^d−|γ|·log(2^d/|γ|)). (5) DegreeSavingMain: there are an even r≥2 and η>0 such that for all d and shapes μ, dim·Re tr((QQ*)^r) ≤ dim^(1−η). (6) FullDensityMain: there is v≥1 such that, for every ε>0 and large d, every shifted law after v·d steps has normalized squared L² density distance (2^d)!·Σ_g(law−1/(2^d)!)² below ε. (7) ForwardMixingMain: there is v≥1 such that for large d every shifted law after v·d steps has total variation below ε. (8) OptimalOrderMain: the mixing time, the least t with distance at most 1/4, is Θ(log 2^d).
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/ThorpRemaining.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/ThorpRemaining.lean; bytes 21058..21252
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_ThorpRemaining

namespace OAI

universe u v

noncomputable section

open scoped BigOperators

open Filter

namespace ThorpResults

theorem remaining_main :
    FrameMain ∧ InformationMain ∧ SpectrumMain ∧ SignedMain ∧
      DegreeSavingMain ∧ FullDensityMain ∧ ForwardMixingMain ∧ OptimalOrderMain := by
  sorry

end ThorpResults
end
end OAI
