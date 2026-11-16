-- Prove2me | Theorems.Thm_MSetBandit_Supplement_theorem_2
-- name    : MSetBandit.Supplement.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T23:49:55.871032+00:00
-- url     : https://prove2.me/theorems/bfc1f170-ecbc-4264-99e4-b9562b8c889d
-- title:
--   Theorem 2 — matching high-probability lower bound $\Omega\big(\sqrt{dT(\log\binom dm+\log(1/\delta))}\big)$
-- statement:
--   There exist universal constants $c>0$ and $\delta_0\in(0,1)$ and a horizon threshold $T(d,m,\delta)$, bounded by a fixed polynomial in $d$, $m$ and $\log(1/\delta)$, such that the following holds. Let $d\ge2$, $1\le m\le d-1$, $\delta\in(0,\delta_0]$ and let $T\ge T(d,m,\delta)$ be an integer horizon. For every randomized algorithm on $\mathcal X_{d,m}$ there exists an adaptive non-anticipating adversary whose action losses lie in $[0,1]$ such that
--   $$
--   \mathbb P\Big(R_T\ \ge\ c\sqrt{dT\Big(\log\binom dm+\log\frac1\delta\Big)}\Big)\ \ge\ \delta .
--   $$
--   Here $R_T$ is the realized regret (4) against the best fixed $m$-set in hindsight, $\mathbb P$ is the law of the algorithm's private randomness, and $\log$ is natural.
--
--   The constants $c$, $\delta_0$, the threshold and the polynomial bounding it are chosen once, before $d$, $m$, $\delta$, $T$ and the algorithm; the adversary is chosen after the algorithm. Together with Theorem 1 this shows that the minimax high-probability regret of adversarial $m$-set bandits is of order $\sqrt{dT(\log K+\log(1/\delta))}$ with $K=\binom dm$.
--
--   **Formalization Note** The adversary is deterministic (a function of the history of actions and scalar feedback), as in the paper's Section 2 model. The private randomness lives on an arbitrary measurable space $\Omega$ with a probability measure; each decision rule is measurable in $\omega$. Rounds are indexed from $0$.
--
--   Differences from the source:
--   - encoding: 1 ≤ m ≤ d − 1 → 1 ≤ m and m + 1 ≤ d (natural numbers); reason: same instances
--   - encoding: every randomized algorithm: private randomness Υ on any probability space, X_t = h_t(H_{t−1}, Υ) with deterministic h_t → every Ω : Type with a probability measure P and every RandAlg (decision rules measurable in ω for each history); reason: measurability is the paper's implicit convention (P(R_T ≥ b) must be defined); Type is Lean's universe of ordinary spaces
--   - encoding: action losses in [0,1] at every round t ∈ [T] along the interaction → 0 ≤ 1_x ⬝ᵥ f_t(H) ≤ 1 for every t < T, every history H of length t and every action x; reason: an adversary can be redefined as 0 on histories that do not occur, so the two requirements are equivalent
--   - encoding: P(R_T ≥ b) over the algorithm's private randomness → P.real {ω | b ≤ runRegret alg adv T ω}; reason: the event is measurable since the history takes finitely many values; P.real is its probability
--   - encoding: rounds t = 1, …, T; items [d] → rounds 0, …, T − 1; items Fin d; reason: index shift only
--   - encoding: there exists an adaptive non-anticipating adversary (ℓ_t F_{t−1}-measurable, with F_t = σ(H_t), pp.4, 40) → there exists a DetAdversary, ℓ_t = f_t(H_{t−1}); reason: F_{t−1} = σ(H_{t−1}) makes ℓ_t a function of H_{t−1}, and p.41 calls this deterministic adversary the one "required by our model"; same class
--   - encoding: a threshold T(d, m, δ) bounded by a polynomial in d, m and log(1/δ) → a function Tth : ℕ → ℕ → ℝ → ℝ and one p : MvPolynomial (Fin 3) ℝ with Tth d m δ ≤ p(d, m, log(1/δ)) for every admissible (d, m, δ); reason: the paper's threshold is used only for admissible (d, m, δ); a real polynomial in three variables is the paper's polynomial bound
-- source:
--   Bacchiocchi–Cesari–Colomboni, An Efficient Minimax-Optimal Algorithm for Adversarial m-Set Bandits, arXiv:2608.12231, Section 5.4, Theorem 2, p.15

import Mathlib
import Definitions.Def_MSetBandit_Supplement_ActionLossesIn01
import Definitions.Def_MSetBandit_Supplement_runRegret
open MeasureTheory

namespace MSetBandit.Supplement

/-- **Theorem 2 (matching high-probability lower bound).** Bacchiocchi–Cesari–Colomboni, *An Efficient Minimax-Optimal Algorithm for Adversarial m-Set Bandits*, arXiv:2608.12231, Theorem 2, Section 5.4, p.15:
"There exist universal constants `c > 0` and `δ0 ∈ (0, 1)` and a threshold `T(d, m, δ)` bounded
by a polynomial in `d`, `m`, and `log(1/δ)` such that the following holds. Let `d ≥ 2`,
`1 ≤ m ≤ d − 1`, `δ ∈ (0, δ0]`, and `T ≥ T(d, m, δ)`. For every randomized algorithm on
`X_{d,m}`, there exists an adaptive non-anticipating adversary whose action losses belong to
`[0, 1]` and such that `P(R_T ≥ c √(dT(log C(d,m) + log(1/δ)))) ≥ δ`."

**Formalization Note.** `c`, `δ0`, the threshold `Tth` and a single real polynomial `p` in three
variables are chosen first; `Tth d m δ ≤ p(d, m, log(1/δ))` for every admissible `(d, m, δ)`.
Then `d, m, δ, T` and the algorithm are arbitrary, and the adversary (deterministic, as in the
Section 2 model) is chosen after the algorithm. The algorithm ranges over every
private-randomness space `Ω : Type` with probability measure `P` and every measurable
history-dependent decision rule. `log` is natural, `C(d,m) = Nat.choose d m`. -/
theorem theorem_2 :
    ∃ c : ℝ, 0 < c ∧ ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 < 1 ∧ ∃ Tth : ℕ → ℕ → ℝ → ℝ,
      (∃ p : MvPolynomial (Fin 3) ℝ, ∀ d m : ℕ, ∀ δ : ℝ, 2 ≤ d → 1 ≤ m → m + 1 ≤ d →
        0 < δ → δ ≤ δ0 →
        Tth d m δ ≤ MvPolynomial.eval ![(d : ℝ), (m : ℝ), Real.log (1 / δ)] p) ∧
      ∀ (d m : ℕ), 2 ≤ d → 1 ≤ m → m + 1 ≤ d → ∀ δ : ℝ, 0 < δ → δ ≤ δ0 →
        ∀ T : ℕ, Tth d m δ ≤ (T : ℝ) →
        ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
          (alg : RandAlg d m Ω),
          ∃ adv : DetAdversary d m, ActionLossesIn01 T adv ∧
            δ ≤ P.real {ω | c *
                Real.sqrt ((d : ℝ) * T * (Real.log (Nat.choose d m) + Real.log (1 / δ)))
              ≤ runRegret alg adv T ω} := by sorry

end MSetBandit.Supplement
