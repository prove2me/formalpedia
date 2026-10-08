-- Prove2me | Theorems.Thm_OAI_CurrentProjection_actualRowMain
-- name    : OAI.CurrentProjection.actualRowMain
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:32:32.128849+00:00
-- url     : https://prove2.me/theorems/5ac4b53b-24e2-4bd9-8e36-9746661e527f
-- statement:
--   The theorem states that, for natural numbers d, m, r, q with admissible dimensions (m, r, q all at least 1, m+r < d-1, and m+r-m-(q-1) at least 1, i.e. r-(q-1) at least 1), and a countable measurable space W with measurable singletons, the following holds. Let P be a probability measure on ((S x W) x R), where S is the unit sphere in R^d and R is the space of m-tuples of vectors in R^d (m rows). Suppose that after regrouping coordinates to (S x R) x W, the (S x R)-marginal equals the product of a probability measure ν on S with the m-fold product of standard Gaussian measures on R^d, and that ν is bounded above by ofReal(H) times the uniform probability measure on the sphere, for some real H. Suppose the Shannon entropy of the W-marginal of P is finite. For each positive-probability value w of W, let ρ(w) be a finite measure on the sphere that is absolutely continuous with respect to the uniform measure, and let B(w), D(w) be positive reals such that ρ(w) has local growth with exponent m+r and constant B(w) (every closed ball of radius t>0 has ρ(w)-measure at most B(w) t^(m+r)) and local growth with exponent d-1 and constant D(w). Extend ρ by the zero measure and B, D by the constant 1 to values of W with zero probability. Assume also that the function (s,w) -> log(1 + e^(9d) B(w)(1 + max(log(D(w)/B(w)),0))) is integrable with respect to the (S x W)-marginal of P. Then the ActualRowConclusion holds for the experiment in which P is combined with r further independent standard Gaussian rows, the observation consists of all m+r rows, the W-value, and the labels given by inner products of the sphere point with each row, and the conditional selection of ρ, B, D is read off from W. It asserts that the relative entropy (KL divergence) of P from the product of its (S x W)-marginal with the Gaussian row law is finite and, in real value, at most the Shannon entropy of the W-marginal; that the conditional law of the labels given the observed rows and W is almost surely absolutely continuous with respect to Lebesgue measure; that the cube averages of ρ at scale 1/j converge almost surely to the exact density; that for every δ>0 the log(1+cube average at scale δ) is integrable and has expectation at most I/q + E, where I is the row relative entropy and E is the expectation of log(1+momentBound(9,d,B,D)) under the (S x W)-marginal; that the same integrability and bound hold for the exact density; that I/q + E is at most (entropy of W)/q + E; and that the positive part of the log of the exact density is integrable, with its extended log-expectation (positive part minus negative part, with value infinite where the density is zero) also at most I/q + E.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/GaussianReplacement.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/GaussianReplacement.lean; bytes 22070..23275
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_GaussianReplacement

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter InformationTheory

open scoped ENNReal NNReal RealInnerProductSpace Topology

noncomputable section

namespace CurrentProjection

theorem actualRowMain {d m r q : ℕ} {W : Type*} [MeasurableSpace W]
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
    ActualRowConclusion (r:=r) (q:=q) P (completeFamily (P.map swapLast).snd ρ 0)
      (completeFamily (P.map swapLast).snd B 1) (completeFamily (P.map swapLast).snd D 1) := by
  sorry

end CurrentProjection
end
end OAI
