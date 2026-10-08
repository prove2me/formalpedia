-- Prove2me | Theorems.Thm_OAI_CurrentProjection_actualRowSourceMain
-- name    : OAI.CurrentProjection.actualRowSourceMain
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:32:32.438661+00:00
-- url     : https://prove2.me/theorems/62fdcb38-c1d5-40b1-8ba0-8dd682143b8d
-- statement:
--   The theorem states the following. Let d, m, r, q be natural numbers with admissible dimensions, meaning m, r, q are each at least 1, m+r < d-1, and m+r-m-(q-1) >= 1. Let W be a countable measurable space with measurable singletons, and let P be a probability measure on triples ((s,w),X), where s lies on the unit sphere in R^d, w is a message in W, and X consists of m rows in R^d. Assume the (s,X)-marginal of P equals ν times the law of m independent standard Gaussian rows, where ν is a probability measure on the sphere with ν <= ofReal(H) times the uniform measure on the sphere, for a real H; the Shannon entropy of the message marginal of P is finite. For each message w of positive probability, let ρ_w be a finite measure on the sphere that is absolutely continuous with respect to the uniform measure, and let B_w, D_w > 0 be constants such that ρ_w has local growth ρ_w(ball of radius t around z) <= B_w t^(m+r) for every center z and every t>0, and also <= D_w t^(d-1). Extend ρ, B, D to all messages by the default values 0, 1, 1 on null messages, and assume that s,w -> log(1 + e^(9d) B_w (1 + max(log(D_w/B_w), 0))) is integrable under the (s,w)-marginal of P. Then, writing I for the conditional mutual information of the rows X and the message w given s, and Λ for the integral of that log term over the (s,w)-marginal, the conclusion is a bundle of statements for the experiment in which X is joined with r further independent standard Gaussian rows and the observation is the m+r rows, the message, and the m+r labels given by inner products of s with the rows. It says that I is finite and at most the Shannon entropy of the message; the conditional law of the labels given rows and message is almost surely absolutely continuous with respect to Lebesgue measure; the cube averages of ρ_w, with cube half-width 1/j, converge almost surely to the exact density as j tends to infinity; for every δ > 0 the log(1 + cube average) is integrable with expectation at most I/q + Λ; log(1 + exact density) is integrable with expectation at most I/q + Λ; I/q + Λ is at most entropy/q + Λ; the positive part of the log exact density is integrable; and the extended expectation of the log exact density is at most I/q + Λ.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/GaussianReplacement.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/GaussianReplacement.lean; bytes 23841..25058
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_GaussianReplacement

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter InformationTheory

open scoped ENNReal NNReal RealInnerProductSpace Topology

noncomputable section

namespace CurrentProjection

theorem actualRowSourceMain {d m r q : ℕ} {W : Type*} [MeasurableSpace W]
    [Countable W] [MeasurableSingletonClass W]
    (hdim : AdmissibleDimensions d m r q)
    (P : Measure ((Sphere d×W)×Rows m d)) [IsProbabilityMeasure P]
    (ν : Measure (Sphere d)) [IsProbabilityMeasure ν]
    (hInd : (P.map swapLast).fst = ν.prod (gaussianRows m d))
    (H : ℝ) (hν : ν ≤ ENNReal.ofReal H • uniformSphere d)
    (hEntropy : shannonEntropy (P.map swapLast).snd ≠ ∞)
    (ρ : PositiveMessage (P.map swapLast).snd → Measure (Sphere d))
    [∀ w, IsFiniteMeasure (ρ w)]
    (_hρac : ∀ w, ρ w ≪ uniformSphere d)
    (B D : PositiveMessage (P.map swapLast).snd → ℝ)
    (hB : ∀ w, 0 < B w) (hD : ∀ w, 0 < D w)
    (hgB : ∀ w, LocalGrowth (ρ w) (m+r) (B w))
    (hgD : ∀ w, LocalGrowth (ρ w) (d-1) (D w))
    (hCI : Integrable (fun sw : Sphere d×W => Real.log (1+momentBound 9 d
      (completeFamily (P.map swapLast).snd B 1 sw.2) (completeFamily (P.map swapLast).snd D 1 sw.2))) P.fst) :
    ActualRowSourceConclusion (r:=r) (q:=q) P (completeFamily (P.map swapLast).snd ρ 0)
      (completeFamily (P.map swapLast).snd B 1) (completeFamily (P.map swapLast).snd D 1) := by
  sorry

end CurrentProjection
end
end OAI
