-- Prove2me | Theorems.Thm_HierADA_Supplement_theorem_5_2
-- name    : HierADA.Supplement.theorem_5_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T05:39:34.286021+00:00
-- url     : https://prove2.me/theorems/eda2db75-65ee-4a33-928f-70310f7bf01b
-- title:
--   Theorem 5.2 — adaptive data analysis on a bounded universe from $O\big((\frac1{\alpha^2}+\min(\frac{\sqrt k}{\alpha},\frac{\sqrt{\ln|U|}}{\alpha^2}))\log^5\frac{2k}{\alpha\xi}\big)$ samples
-- statement:
--   There is a universal constant $C$ with the following property. Let $U$ be a known finite nonempty universe, let $\alpha\in(0,1)$ be an accuracy parameter, $\xi\in(0,1)$ a failure probability and $k\ge1$ an integer query budget. Then there are a sample size
--
--   $$
--   N\le C\Big(\frac1{\alpha^2}+\min\Big(\frac{\sqrt k}{\alpha},\ \frac{\sqrt{\ln|U|}}{\alpha^2}\Big)\Big)\log^5\frac{2k}{\alpha\xi},
--   $$
--
--   a probability space of seeds and a randomized mechanism on $N$ samples such that, for every distribution $D$ on $U$ and every adaptive analyst submitting queries $f_t:U\to[0,1]$ (each depending on all previous queries and answers),
--
--   $$
--   \Pr_{S\sim D^N,\ \omega}\Big[\big|a_t-\mathbb E_{X\sim D}f_t(X)\big|\le\alpha\ \text{for all }t\le k\Big]\ge1-\xi .
--   $$
--
--   Moreover, the failure event is measurable in the seed.
--
--   Compared with the main theorem of the paper (Theorem 3.8, which holds for every finite domain with a sample size independent of the domain), a known universe lets the mechanism learn the population distribution itself, and the $\sqrt k/\alpha$ term is replaced by $\sqrt{\ln|U|}/\alpha^2$ whenever that is smaller.
--
--   **Formalization Note** The constant $C$ is chosen before the universe and the parameters. Since $U$ is known, the sample size, the seed space and the mechanism may depend on $U$, but never on $D$ or on the analyst. "The mechanism in Figure 3" is stated existentially, because Figure 3 is built from an instance of Corollary 3.9, which the paper states existentially. Analysts are deterministic maps from the history to the next query; the interaction, the population mean and the error event are those of the published `IsRandomnessNecessaryADA.Plain`, and the failure probability is the base mission's `HierADA.failureProb`. $\ln$ and $\log$ are natural logarithms.
--
--   Differences from the source:
--   - reading: the mechanism in Figure 3 → there exists a randomized mechanism (seed space and mechanism chosen after U, α, ξ, k, before D and the analyst); reason: Figure 3 is built on the existential Corollary 3.9 instance, so the theorem's content is existence of such a mechanism (as the informal Theorem 1.5 says); the quantifier order keeps the mechanism independent of D
--   - reading: a randomized mechanism; adaptively chosen queries → a seed drawn once from a probability space, each answer a deterministic function of (seed, sample, history, current query); analysts deterministic maps from the history to the next query; reason: the same model as the published goal HierADA.theorem_3_8; Figure 3's randomness is that of C and can be pre-assigned
--   - reading: with probability at least 1 − ξ → failureProb ≤ ξ: the sum over samples of D^N(s) times the seed measure of the bad section (outer measure); reason: the product law on a finite sample space; with measurable sections it is the ordinary probability
--   - encoding: the probability of the failure event (implicit) → an added clause: every section of the failure event is measurable in the seed; reason: the paper presupposes the event has a probability; same clause as HierADA.theorem_3_8
--   - encoding: O(·), ln, log → one constant C quantified before U, α, ξ, k; natural logarithm; reason: the standard meaning of O; another base changes only C
--   - encoding: a known finite nonempty universe U, every distribution D on U → ∀ X with Fintype X and Nonempty X, ∀ P : PMF X; reason: same quantifiers
-- source:
--   Gribelyuk–Lin–Lyu–Majid–Woodruff–Yu–Zhou, Adaptive Data Analysis and Adversarial Robustness on Insertion-Deletion Streams, preprint (version of 2026-11-03, sha256 f220ae51…), Theorem 5.2, pp.42–43 (PDF pp.43–44); mechanism Figure 3, p.41; formal version of Theorem 1.5, p.5

import Mathlib
import Definitions.Def_IsRandomnessNecessaryADA_Plain_Protocol
import Definitions.Def_HierADA_RandMechanism
import Definitions.Def_HierADA_failureProb

set_option autoImplicit false

open MeasureTheory IsRandomnessNecessaryADA.Plain

namespace HierADA.Supplement

/-- **Theorem 5.2 (Adaptive data analysis on a bounded universe)** —
Gribelyuk–Lin–Lyu–Majid–Woodruff–Yu–Zhou, *Adaptive Data Analysis and Adversarial Robustness on
Insertion-Deletion Streams*, preprint (version of 2026-11-03, sha256 f220ae51…), Theorem 5.2,
pp.42–43 (PDF pp.43–44); formal version of Theorem 1.5, p.5.

There is a universal constant `C` such that for every known finite nonempty universe `X`, every
accuracy `α ∈ (0, 1)`, failure probability `ξ ∈ (0, 1)` and query budget `k ≥ 1`, there are a
sample size
`N ≤ C (1/α² + min(√k/α, √(ln |X|)/α²)) log⁵(2k/(αξ))`, a seed probability space and a randomized
mechanism on `N` samples such that, for every distribution `P` on `X` and every adaptive analyst,
with probability at least `1 − ξ` over the sample and the seed, all `k` answers satisfy
`|a_t − E_{X∼P} f_t(X)| ≤ α`.

**Formalization Note.** O(·) is one constant `C` chosen before the universe, `α`, `ξ` and `k`.
The universe is known, so the sample size, the seed space and the mechanism may depend on `X`
(the Figure 3 mechanism starts from the uniform distribution on `X`); none of them depends on the
distribution `P` or on the analyst. "The mechanism in Figure 3" is stated existentially: Figure 3
is built from an instance of Corollary 3.9, which the paper itself states existentially.
Analysts are deterministic maps from the history to the next query (published `Analyst`); the
interaction, the population mean and the error event (error `> α` is a failure) are those of
`IsRandomnessNecessaryADA.Plain`; the failure probability is the base mission's `failureProb`.
`ln` and `log` are the natural logarithm. As in `HierADA.theorem_3_8`, every seed section of the
failure event is required to be measurable, so that its probability is defined. -/
theorem theorem_5_2 :
    ∃ C : ℝ, ∀ (X : Type) [Fintype X] [Nonempty X],
      ∀ α ξ : ℝ, 0 < α → α < 1 → 0 < ξ → ξ < 1 → ∀ k : ℕ, 1 ≤ k →
      ∃ N : ℕ, (N : ℝ) ≤ C * (1 / α ^ 2 +
          min (Real.sqrt k / α) (Real.sqrt (Real.log (Fintype.card X)) / α ^ 2)) *
          Real.log (2 * k / (α * ξ)) ^ 5 ∧
      ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω), IsProbabilityMeasure μ ∧
        ∃ M : RandMechanism Ω X N,
          (∀ (P : PMF X) (A : Analyst X) (s : Fin N → X),
            MeasurableSet {ω | interaction (M ω) A s k ∈ errorEvent P α}) ∧
          ∀ (P : PMF X) (A : Analyst X), failureProb μ M P A α k ≤ ENNReal.ofReal ξ := by sorry

end HierADA.Supplement
