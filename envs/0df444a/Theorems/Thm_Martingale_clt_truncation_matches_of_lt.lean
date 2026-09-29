-- Prove2me | Theorems.Thm_Martingale_clt_truncation_matches_of_lt
-- name    : Martingale.clt_truncation_matches_of_lt
-- status  : Proved
-- author  : @LukeBernese
-- created : 2026-08-15T18:48:57.271275+00:00
-- url     : https://prove2.me/theorems/89cf17cb-bb45-43d5-b06c-4eb7788247a8
-- title:
--   Step 0 of the martingale CLT: truncation at level 2 is asymptotically harmless
-- statement:
--   First step of the proof of the martingale CLT. Replace the difference array $D_{n,k}$ by its truncation
--
--   $$Z_{n,k} = D_{n,k}\,\mathbf{1}\Bigl\{\textstyle\sum_{j<k} D_{n,j}^2 \le 2\Bigr\}.$$
--
--   The indicator depends only on $D_{n,j}$ for $j < k$, so it is measurable with respect to the past and $\{Z_{n,k}\}$ is again a martingale difference array — that is exactly why the sum inside the indicator stops *before* $k$. The claim is that this substitution does not change the limit: the difference of the two row sums tends to $0$ in probability.
--
--   The reason is that the two row sums coincide on the event that the running sum of squares never exceeds the threshold, and under the limiting-variance hypothesis $\sum_{k<n} D_{n,k}^2 \Rightarrow \sigma^2$ with $\sigma^2 < 2$ that event has probability tending to one. The purpose of the truncation is to make the increments bounded, so that the expansion of the characteristic function in the main argument converges.
--
--   **The hypothesis $\sigma^2 < 2$ is necessary, not cosmetic.** If the limiting variance exceeded the truncation level the indicator would switch off with asymptotically positive probability and the two row sums would genuinely differ. The classical presentations take $\sigma \equiv 1$ without loss of generality — one may always rescale — and the threshold $2$ is then simply a fixed constant comfortably above $1$; stating the lemma for general $\sigma$ requires carrying that inequality explicitly. This supersedes an earlier version of this statement which omitted it and is therefore false for $\sigma^2 > 2$.
-- source:
--   B. M. Brown, "Martingale Central Limit Theorems", Annals of Mathematical Statistics 42 (1971) 59-66, Theorem 2; D. L. McLeish, "Dependent Central Limit Theorems and Invariance Principles", Annals of Probability 2 (1974) 620-628, Theorem 2.3; P. Hall and C. C. Heyde, Martingale Limit Theory and Its Application, Academic Press 1980, Theorem 3.2 and its proof.

import Mathlib.Probability.Martingale.Basic
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Probability.Distributions.Gaussian.Real

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology ProbabilityTheory

theorem Martingale.clt_truncation_matches_of_lt {Ω : Type*} {m0 : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] (D : ℕ → ℕ → Ω → ℝ)
    (hmeas : ∀ n k, Measurable (D n k))
    (σ : ℝ) (hσ2 : σ ^ 2 < 2)
    (hvar : TendstoInMeasure P
      (fun (n : ℕ) ω => ∑ k ∈ Finset.range n, D n k ω ^ 2) atTop (fun _ => σ ^ 2)) :
    TendstoInMeasure P
      (fun (n : ℕ) ω => (∑ k ∈ Finset.range n, D n k ω)
        - ∑ k ∈ Finset.range n, (Set.indicator
            {ω' | ∑ j ∈ Finset.range k, D n j ω' ^ 2 ≤ 2} (D n k) ω))
      atTop (fun _ => 0) := by sorry
