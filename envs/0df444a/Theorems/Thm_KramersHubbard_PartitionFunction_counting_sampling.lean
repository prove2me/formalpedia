-- Prove2me | Theorems.Thm_KramersHubbard_PartitionFunction_counting_sampling
-- name    : KramersHubbard.PartitionFunction.counting_sampling
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:06:48.119565+00:00
-- url     : https://prove2.me/theorems/d08550d9-313d-4814-ad19-95ff8e896e56
-- title:
--   Lemma 11 — Independent inverse product estimation
-- statement:
--   For an attractive Kramers input with $\beta>0$ and $M\ge1$, use the interaction-strength schedule in Appendix B and let $k\ge1$ be its computed number of positive stages. Let $0<\varepsilon\le1$ and
--
--   $$n=\left\lceil\frac{64ek}{\varepsilon^2}\right\rceil.$$
--
--   At stage $i$ draw $n$ samples independently from a probability law whose total variation distance from $\mu_{t_i}$ is at most $1/(8kn)$. The entire sample array is independent across stages as well. For the actual empirical inverse product $\widehat W$, with zero product declared a failure,
--
--   $$\Pr\big[(1-\varepsilon)W(1)\le\widehat W\le(1+\varepsilon)W(1)\big]\ge\frac34.$$
--
--   The target $W(1)$ is positive real and is computed from the concrete principal minors. Sample laws are legitimate hypotheses of this statistical lemma; they are not hypotheses of the mission goal.
--
--   Differences from the source:
--   - reading: the statement says samples are independent at each strength and the proof calls the averages independent → a product probability law over the entire array of stages and samples; reason: the variance calculation on p.30 and the joint coupling on p.31 use independence across stages as well as within each stage
--   - encoding: the capped geometric schedule, ceiling sample count and reciprocal of the product of empirical means → a logarithmic ceiling gives the actual stage count, finite sums give the complete array law, and a zero product returns zero as failure; reason: this represents exactly the stated schedule and estimator, including t=0, empty subsets and all zero couplings
-- source:
--   Chaithanya Rayudu, Jun Takahashi, Ojas Parekh, Andrew Zhao, STOC 2027 submission #1325 (October 2026), Efficient classical simulation of Fermi-Hubbard models with Kramers symmetry, Lemma 11 and Eqs.(61)-(65), pp.30-31; Eq.(34), p.15; printed page = 1-based PDF page. https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1325.pdf; PDF SHA-256 e3fd3fa7390d8ff9f0f1e2ee07e6ebc5b8d7304e26be9e76959d9587f4564eae. Canonical submitted artifact, citation_basis: published; title-page date November 3, 2026; no assertion of conference acceptance.

import Definitions.Def_KramersHubbard_PartitionFunction_Counting

noncomputable section
open scoped BigOperators
open Matrix MeasureTheory

namespace KramersHubbard.PartitionFunction

/-- Lemma 11 and its actual schedule/estimator, Appendix B, pp.30-31.
    Independence is represented by the product probability of the whole array. -/
theorem counting_sampling {N r M : ℕ} (D : Data N r) (hD : Attractive D)
    (β : ℝ) (hβ : 0 < β) (hM : 0 < M) (eps : ℝ) (heps : 0 < eps ∧ eps ≤ 1) :
    let k := stageCount D β M
    let n := sampleCount k eps
    ∀ nu : Fin k → Finset (Insertion M r) → ℝ,
      (∀ i X, 0 ≤ nu i X) → (∀ i, ∑ X, nu i X = 1) →
      (∀ i, (1/2 : ℝ) * ∑ X : Finset (Insertion M r),
        ‖(nu i X : ℂ) - countingLaw D β (strength D β M (i.val+1)) X‖ ≤
          1 / (8 * (k : ℝ) * n)) →
      ∃ W : ℝ, 0 < W ∧ countingW (M := M) D β 1 = (W : ℂ) ∧
        (∑ xs : Fin k → Fin n → Finset (Insertion M r),
          if (1-eps)*W ≤ productEstimate (strength D β M) xs ∧
              productEstimate (strength D β M) xs ≤ (1+eps)*W
          then arrayProbability nu xs else 0) ≥ 3/4 := by sorry

end KramersHubbard.PartitionFunction
