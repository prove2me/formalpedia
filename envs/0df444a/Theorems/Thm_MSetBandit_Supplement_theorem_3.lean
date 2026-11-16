-- Prove2me | Theorems.Thm_MSetBandit_Supplement_theorem_3
-- name    : MSetBandit.Supplement.theorem_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T23:49:06.027681+00:00
-- url     : https://prove2.me/theorems/9c4a9fc4-7019-4826-9c8a-1144be56a196
-- title:
--   Theorem 3 — explicit lower bound: $\mathbb P\big(R_T\ge2^{-43}\sqrt{dT(\log\binom dm+\log(1/\delta))}\big)\ge\delta$
-- statement:
--   Let $d\ge2$ and $1\le m\le d-1$ be integers, let $\delta\in(0,2^{-36}]$, and let $T$ be an integer horizon with
--   $$
--   T\ \ge\ \Big\lceil 64d^2+4d\,\min\{m,d-m\}^2\log(1/\delta)\Big\rceil .
--   $$
--   Then for every randomized algorithm on $\mathcal X_{d,m}$ (any private randomness $\Upsilon$ with law $\mathbb P$, any history-dependent decision rules) there exists a deterministic adaptive non-anticipating adversary whose action losses lie in $[0,1]$ such that
--   $$
--   \mathbb P\Big(R_T\ \ge\ 2^{-43}\sqrt{dT\Big(\log\binom dm+\log\frac1\delta\Big)}\Big)\ \ge\ \delta .
--   $$
--   Here $R_T$ is the realized regret (4) against the best fixed $m$-set in hindsight and $\log$ is the natural logarithm. The adversary may depend on the algorithm.
--
--   This is the fully explicit form of the paper's matching lower bound: it shows that the high-probability upper bound $O\big(\sqrt{dT(\log K+\log(1/\delta))}\big)$ of Theorem 1 is optimal up to a universal constant, in both the $\log K$ and the $\log(1/\delta)$ dependence.
--
--   **Formalization Note** The private randomness lives on an arbitrary measurable space $\Omega$ with a probability measure; each decision rule is measurable in $\omega$. The adversary is a deterministic function of the history of actions and scalar feedback. Rounds are indexed from $0$.
--
--   Differences from the source:
--   - encoding: 1 ≤ m ≤ d − 1 → 1 ≤ m and m + 1 ≤ d (natural numbers); reason: same instances
--   - encoding: every randomized algorithm: private randomness Υ on any probability space, X_t = h_t(H_{t−1}, Υ) with deterministic h_t → every Ω : Type with a probability measure P and every RandAlg (decision rules measurable in ω for each history); reason: measurability is the paper's implicit convention (P(R_T ≥ b) must be defined); Type is Lean's universe of ordinary spaces
--   - encoding: action losses in [0,1] at every round t ∈ [T] along the interaction → 0 ≤ 1_x ⬝ᵥ f_t(H) ≤ 1 for every t < T, every history H of length t and every action x; reason: an adversary can be redefined as 0 on histories that do not occur, so the two requirements are equivalent
--   - encoding: P(R_T ≥ b) over the algorithm's private randomness → P.real {ω | b ≤ runRegret alg adv T ω}; reason: the event is measurable since the history takes finitely many values; P.real is its probability
--   - encoding: rounds t = 1, …, T; items [d] → rounds 0, …, T − 1; items Fin d; reason: index shift only
--   - encoding: T ≥ ⌈64d² + 4d min{m, d − m}² log(1/δ)⌉ → ⌈64d² + 4d·min(m, d − m)²·log(1/δ)⌉ ≤ (T : ℤ); reason: the same integer comparison
-- source:
--   Bacchiocchi–Cesari–Colomboni, An Efficient Minimax-Optimal Algorithm for Adversarial m-Set Bandits, arXiv:2608.12231, Appendix E, Theorem 3, p.40 (restated in E.4, p.56; proof pp.56–57)

import Mathlib
import Definitions.Def_MSetBandit_Supplement_ActionLossesIn01
import Definitions.Def_MSetBandit_Supplement_runRegret
open MeasureTheory

namespace MSetBandit.Supplement

/-- **Theorem 3 (explicit high-probability lower bound).** Bacchiocchi–Cesari–Colomboni, *An Efficient Minimax-Optimal Algorithm for Adversarial m-Set Bandits*, arXiv:2608.12231, Theorem 3, Appendix E, p.40
(restated in E.4, p.56): "Let `d ≥ 2`, `1 ≤ m ≤ d − 1`, and `δ ∈ (0, 2^{−36}]`, and assume that
`T ≥ ⌈64d² + 4d min{m, d − m}² log(1/δ)⌉`. Then, for every randomized algorithm on `X_{d,m}`,
there exists a deterministic adaptive non-anticipating loss process whose action losses belong to
`[0, 1]` and such that `P(R_T ≥ 2^{−43} √(dT(log C(d,m) + log(1/δ)))) ≥ δ`."

**Formalization Note.** `1 ≤ m ≤ d − 1` is `1 ≤ m`, `m + 1 ≤ d`. The algorithm ranges over every
private-randomness space `Ω : Type` with probability measure `P` (the law of `Υ`) and every
measurable history-dependent decision rule (`RandAlg`); the adversary is chosen after the
algorithm. `log` is the natural logarithm, `C(d,m) = Nat.choose d m`. The event is measurable
(the history takes finitely many values); `P.real` is its probability. -/
theorem theorem_3 (d m : ℕ) (hd : 2 ≤ d) (hm : 1 ≤ m) (hmd : m + 1 ≤ d) (δ : ℝ) (hδ0 : 0 < δ)
    (hδ : δ ≤ (2 : ℝ) ^ (-36 : ℤ)) (T : ℕ)
    (hT : ⌈64 * (d : ℝ) ^ 2 + 4 * (d : ℝ) * ((min m (d - m) : ℕ) : ℝ) ^ 2 * Real.log (1 / δ)⌉
      ≤ (T : ℤ))
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (alg : RandAlg d m Ω) :
    ∃ adv : DetAdversary d m, ActionLossesIn01 T adv ∧
      δ ≤ P.real {ω | (2 : ℝ) ^ (-43 : ℤ) *
          Real.sqrt ((d : ℝ) * T * (Real.log (Nat.choose d m) + Real.log (1 / δ)))
        ≤ runRegret alg adv T ω} := by sorry

end MSetBandit.Supplement
