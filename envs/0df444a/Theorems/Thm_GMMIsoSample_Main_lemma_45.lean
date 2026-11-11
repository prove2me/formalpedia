-- Prove2me | Theorems.Thm_GMMIsoSample_Main_lemma_45
-- name    : GMMIsoSample.Main.lemma_45
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T21:33:31.874753+00:00
-- url     : https://prove2.me/theorems/90cfba64-2c5f-43a9-998f-4aeb643e2b2c
-- title:
--   Lemma 45 — TV-close prior-averaged sample laws rule out distinguishing and ε-estimation with T samples
-- statement:
--   Let $F_0,F_1$ be families of probability distributions on $\mathbb R^d$ with $d_{iso}(F_0,F_1)>2\varepsilon$, and let $A_b$ be a prior supported on $F_b$ ($b\in\{0,1\}$). If
--   $$d_{TV}\big(P^{(T)}_{A_0},P^{(T)}_{A_1}\big)\le\frac12,$$
--   then there is no $\varepsilon$-distinguisher for $(F_0,F_1)$ using $T$ sample points, and no $\varepsilon$-density estimator up to isometry using $T$ sample points (with any number $k_{\max}$ of output components) that succeeds with probability at least $9/10$ on every target in $F_0\cup F_1$.
--
--   This is the reduction behind all three lower-bound constructions.
--
--   Differences from the source:
--
--   - encoding: a prior distribution A_b supported on F_b → a probability measure on Measure(ℝ^d) (Giry σ-algebra) with D ∈ F_b for A_b-almost every D; reason: a prior on target distributions; 'supported on' = full measure
--   - encoding: F₀, F₁ families of distributions; d_iso(F₀, F₁) > 2ε → F false, F true sets of probability measures; ENNReal.ofReal (2ε) < disoFam (F false) (F true) in [0, ∞]; reason: the infimum over families is taken in [0, ∞] so that it is not a junk value
--   - encoding: a randomized algorithm (estimator / distinguisher) using T sample points → a Markov kernel from (ℝ^d)^T to its outputs; reason: the kernel is the law of the output given the sample, i.e. the algorithm's internal randomness; the success probability is the joint law of samples and randomness
--   - encoding: with probability at least 1 − q → the measure of the failure set is at most q (its outer measure if the set is not measurable); reason: equal to the probability statement whenever the failure set is measurable, and the stronger statement otherwise
-- source:
--   Chen, De, Lee, Servedio, Sublinear Sample Size Suffices for Learning Mixtures of Gaussians up to Isometry, STOC 2027 submission (version of November 3, 2026, sha256 411f3581…), p. 64, Lemma 45 (Definition 43 and (104), p. 63)

import Mathlib
import Definitions.Def_PolySampIso_Divergences
import Definitions.Def_GMMIsoSample_Main_Model
import Definitions.Def_GMMIsoSample_Main_LowerBound

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace GMMIsoSample.Main

/-- Lemma 45 (p. 64): let `F₀ = F false`, `F₁ = F true` be families of probability distributions
on `ℝ^d` with `d_iso(F₀, F₁) > 2ε`, and `A_b` a prior supported on `F_b`. If
`d_TV(P_{A₀}^(T), P_{A₁}^(T)) ≤ 1/2` (105), then there is no `ε`-distinguisher for `(F₀, F₁)` using
`T` sample points, and no `ε`-density estimator up to isometry using `T` sample points (with any
number `kmax` of output components) that succeeds with probability at least `9/10` on every target
in `F₀ ∪ F₁`. -/
theorem lemma_45 (d T : ℕ) (ε : ℝ) (F : Bool → Set (Measure (E d)))
    (hF : ∀ b, ∀ D ∈ F b, IsProbabilityMeasure D)
    (hsep : ENNReal.ofReal (2 * ε) < disoFam (F false) (F true))
    (A : Bool → Measure (Measure (E d))) (hA : ∀ b, IsProbabilityMeasure (A b))
    (hsupp : ∀ b, ∀ᵐ D ∂(A b), D ∈ F b)
    (hTV : PolySampIso.tvDist (priorAvg (A false) T) (priorAvg (A true) T) ≤ 1 / 2) :
    (¬ ∃ κ : Kernel (Fin T → E d) Bool, IsDistinguisher F T κ) ∧
      ∀ (kmax : ℕ) (K : Kernel (Fin T → E d) (Params d kmax)), IsMarkovKernel K →
        ¬ ∀ b, ∀ D ∈ F b, Succeeds ε T K D := by sorry

end GMMIsoSample.Main
