-- Prove2me | Theorems.Thm_MetricTesting_Characterization_lazy_permutation_coupling
-- name    : MetricTesting.Characterization.lazy_permutation_coupling
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:37:49.027517+00:00
-- url     : https://prove2.me/theorems/6c44787e-204a-418f-bb47-890a68500e43
-- title:
--   Lemma 3.1 — Lazy permutation coupling
-- statement:
--   Let $n\ge r$ and let $D$ be an arbitrary $\Lambda$-valued array, where $\Lambda\subseteq\mathbb R_{\ge0}$ is nonempty. Fix an adaptive decision tree which touches at most $r$ labels on every input. Compare uniform permutation of all $n$ labels with choosing a uniform $r$-set and assigning new labels to uniform unused sampled elements. Then
--   $$\mathcal L(\text{permutation transcript})=\mathcal L(\text{lazy transcript}).$$
--   Moreover, the experiments admit a coupling with the same ordered sequence of images of newly touched labels. No finite query cap is assumed: transcripts include every prefix, so equality covers arbitrarily long runs and stopping decisions. Repeated queries reuse assigned images. The coupling also has equal complete transcripts on its support. This is the sampling identity needed to handle adaptivity without restricting answers to a finite alphabet.
--
--   Differences from the source:
--   - encoding: matrices on [n] with off-diagonal values in Λ and zero diagonal → functions from two-element subsets of Fin n to the subtype Λ of nonnegative reals; reason: this is a bijective encoding of all source matrices; relabelling uses injections and no metric axiom is imposed
--   - encoding: a uniform r-set and successive uniform unused images → a uniform injection Fin r into Fin n, used in first-touch order; reason: each r-set has exactly r! enumerations; revealing their positions sequentially gives precisely the source conditional sampling law
--   - encoding: answer transcripts and coupled newly touched images → the whole sequence of finite histories and stop decisions, and an explicit coupling table; reason: a deterministic rule makes query choices and stop decisions functions of answers; uniform finite marginals represent exactly the source coupling
-- source:
--   Zihan Tan, Theo Teske, STOC 2027 submission #385 (October 2026), p. 9, Lemma 3.1 (PDF p. 10)

import Definitions.Def_MetricTesting_Characterization_sampling

set_option autoImplicit false

noncomputable section

namespace MetricTesting.Characterization

/-- Lemma 3.1, printed p.9 / PDF p.10. Both the whole-transcript law
and a coupling of the complete new-image streams are retained. -/
theorem lazy_permutation_coupling (Λ : Set NNReal) (hΛ : Λ.Nonempty)
    (n r : ℕ) (hn : 1 ≤ n) (hr : r ≤ n) (T : DecisionTree Λ n) (hT : TouchesAtMost T r)
    (D : Array Λ n) :
    uniformImage (permutationTrace D T) = uniformImage (lazyTrace hΛ (r := r) D T) ∧
      ImageCoupling hΛ (r := r) D T := by sorry

end MetricTesting.Characterization
