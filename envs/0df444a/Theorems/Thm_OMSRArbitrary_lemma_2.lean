-- Prove2me | Theorems.Thm_OMSRArbitrary_lemma_2
-- name    : OMSRArbitrary.lemma_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:37:55.642962+00:00
-- url     : https://prove2.me/theorems/266c43e5-c9a4-4d5a-804d-745d9f535260
-- title:
--   Lemma 2 — the independent and correlated models give every policy the same law
-- statement:
--   Consider an instance with weights $r_i>0$ and success probabilities $p_{it}\in(0,1]$. In the independent model each edge $(i,t)$ succeeds independently with probability $p_{it}$; in the correlated model thresholds $z_t$ are i.i.d. uniform on $[0,1]$ and $(i,t)$ succeeds iff $z_t\le p_{it}$.
--
--   **Lemma 2.** For every (possibly randomized) non-anticipative policy, the joint law of its sequence of probes and outcomes, and hence the law of its value, is the same in the independent and the correlated models:
--
--   1. for every transcript $h$, $\Pr_{\mathrm{ind}}[\text{transcript}=h]=\Pr_{\mathrm{corr}}[\text{transcript}=h]$;
--   2. for every set $B\subseteq\mathbb R$, $\Pr_{\mathrm{ind}}[\text{value}\in B]=\Pr_{\mathrm{corr}}[\text{value}\in B]$.
--
--   This is what allows the analysis to work in the correlated model, in which PG and OPT are coupled through the same thresholds.
--
--   **Formalization Note** A randomized policy is a measurable family of deterministic policies indexed by its internal randomness $\xi\sim\mu$.
--
--   Differences from the source:
--   - encoding: a finite set U of resources and arrivals t ∈ [T] = {1, …, T} → resources Fin n and arrivals Fin m, 0-based, for every n, m; reason: relabelling; every finite instance, including empty ones, is covered
--   - encoding: edge probabilities p_it ∈ (0,1] and weights r_i > 0 → the published Instance (r ≥ 0, p ∈ [0,1] on edges) with hypotheses 0 < r_k and 0 < p_e for e ∈ E; reason: the same instances
--   - encoding: a possibly randomized non-anticipative policy → a family ξ ↦ π ξ of deterministic policies, measurable history by history, with ξ ∼ μ a probability measure; reason: the internal randomness ξ of the proof (p.38); a randomized policy is a deterministic one given ξ
--   - encoding: the law of its value → the probability that the value lies in B, for every set B ⊆ ℝ; reason: this determines the law; the value takes finitely many values
--   - generalization: at each step the policy stops or probes an edge (i, t) with i available and t unprobed → the policy may also take the action (t, none), marking t probed without a probe, and an illegal action stops it (published legalize D false); reason: a larger class of policies; the source policies are those that never use these options
-- source:
--   Udwani, Online Matching with Arbitrary Stochastic Rewards, arXiv:2611.03598, Lemma 2, p.11 (proof in App. E, pp.37–38)

import Mathlib
import Definitions.Def_OMSRArbitrary_Policies

open scoped BigOperators
open MeasureTheory
open StochasticRewardMatching.Decomposable (Instance Seeds seedLaw edgeAverage DetPolicy History Action)
noncomputable section

namespace OMSRArbitrary

/-- **Lemma 2** (arXiv:2611.03598, p.11; proof in App. E, pp.37–38): for every non-anticipative
policy, the joint law of its sequence of probes and outcomes, and hence the law of its value, is
the same in the independent and the correlated models.

A possibly randomized policy is a family `π ξ` of deterministic policies indexed by its internal
randomness `ξ ∼ μ` (the proof conditions on `ξ`). Clause 1: every transcript `h` has the same
probability in both models. Clause 2: for every set `B` of reals, the value lies in `B` with the
same probability. The independent model averages over the edge outcomes (published
`edgeAverage`); the correlated model integrates over the thresholds `z ∼ seedLaw m`.

**Formalization Note.** Policies have no ordering restriction (`legalize D false`), which covers
online policies; `ξ ↦ π ξ` is required to be measurable history by history. -/
theorem lemma_2 {n m : ℕ} (D : Instance n m) (hr : ∀ k, 0 < D.reward k)
    (hp : ∀ e ∈ D.edges, 0 < D.probability e)
    {Ξ : Type*} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (π : Ξ → DetPolicy n m)
    (hπ : ∀ (h : History n m) (a : Option (Action n m)), MeasurableSet {ξ | π ξ h = a}) :
    (∀ h : History n m,
      ∫ ξ, edgeAverage D (fun ω => if transcript D (π ξ) ω = h then (1 : ℝ) else 0) ∂μ =
        ∫ ξ, (∫ z, (if transcript D (π ξ) (corrOutcome D z) = h then (1 : ℝ) else 0)
          ∂seedLaw m) ∂μ) ∧
    (∀ B : Set ℝ,
      ∫ ξ, edgeAverage D
          (fun ω => B.indicator (fun _ => (1 : ℝ)) (historyValue D (transcript D (π ξ) ω))) ∂μ =
        ∫ ξ, (∫ z, B.indicator (fun _ => (1 : ℝ))
          (historyValue D (transcript D (π ξ) (corrOutcome D z))) ∂seedLaw m) ∂μ) := by sorry

end OMSRArbitrary
