-- Prove2me | Theorems.Thm_GMMIsoSample_Main_lemma_18
-- name    : GMMIsoSample.Main.lemma_18
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T21:32:12.50337+00:00
-- url     : https://prove2.me/theorems/1b794695-f349-4cb0-a9cb-3542981d2ee1
-- title:
--   Lemma 18 — [ABH+20]: mixtures of at most K spherical Gaussians are properly learnable to TV η from Õ(Kd/η²) samples
-- statement:
--   There are absolute constants $C>0$ and $a\ge0$ such that for every $K$, $d$ and $0<\eta<1$ there is a randomized algorithm using
--   $$T\le C\,\frac{Kd}{\eta^2}\Big(\log\frac{2Kd}{\eta}\Big)^a$$
--   sample points which, for every mixture $D$ of at most $K$ spherical Gaussians in $\mathbb R^d$, outputs with probability at least $9/10$ a mixture $\hat D$ of at most $K$ spherical Gaussians with $d_{TV}(D,\hat D)\le\eta$.
--
--   This handles the regime $\Gamma_{\min}\le\mathrm{polylog}(d)$ of the upper bound, where $\tilde O(d)$ samples are optimal.
--
--   Differences from the source:
--
--   - reading: Õ(Kd/η²) → C (Kd/η²)(log(2Kd/η))^a with absolute C > 0, a ≥ 0; reason: Õ suppresses polylogarithmic factors in the parameters of the bound
--   - encoding: a mixture of at most K spherical Gaussians (target and output) → a valid K-slot parameter tuple (weights ≥ 0 summing to 1, radii > 0; unused slots have weight 0); reason: the same set of distributions
--   - encoding: a randomized algorithm (estimator / distinguisher) using T sample points → a Markov kernel from (ℝ^d)^T to its outputs; reason: the kernel is the law of the output given the sample, i.e. the algorithm's internal randomness; the success probability is the joint law of samples and randomness
--   - encoding: with probability at least 1 − q → the measure of the failure set is at most q (its outer measure if the set is not measurable); reason: equal to the probability statement whenever the failure set is measurable, and the stronger statement otherwise
-- source:
--   Chen, De, Lee, Servedio, Sublinear Sample Size Suffices for Learning Mixtures of Gaussians up to Isometry, STOC 2027 submission (version of November 3, 2026, sha256 411f3581…), p. 34, Lemma 18

import Mathlib
import Definitions.Def_PolySampIso_Divergences
import Definitions.Def_GMMIsoSample_Main_Model

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace GMMIsoSample.Main

/-- Lemma 18 (p. 34, from [ABH+20]): for every `K`, `d` and `0 < η < 1`, a mixture of at most `K`
spherical Gaussians in `ℝ^d` can be learned to total variation distance `η` from `Õ(Kd/η²)` sample
points with success probability at least `9/10`, the output being a mixture of at most `K`
spherical Gaussians. `Õ(Kd/η²)` is read as `C (Kd/η²) (log(2Kd/η))^a` with absolute `C > 0`,
`a ≥ 0`. A mixture of at most `K` components is a valid `K`-slot parameter tuple (slots of weight
`0` are absent components). -/
theorem lemma_18 :
    ∃ C a : ℝ, 0 < C ∧ 0 ≤ a ∧ ∀ (K d : ℕ) (η : ℝ), 0 < η → η < 1 →
      ∃ T : ℕ, (T : ℝ) ≤ C * ((K : ℝ) * d / η ^ 2) * Real.log (2 * K * d / η) ^ a ∧
        ∃ Ker : Kernel (Fin T → E d) (Params d K), IsMarkovKernel Ker ∧
          ∀ p : Params d K, IsValidParams p →
            (iidLaw (mix p) T).bind Ker
              {h | ¬ (IsValidParams h ∧ PolySampIso.tvDist (mix p) (mix h) ≤ η)} ≤ 1 / 10 := by sorry

end GMMIsoSample.Main
