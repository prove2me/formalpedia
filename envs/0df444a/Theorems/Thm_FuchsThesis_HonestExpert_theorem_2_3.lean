-- Prove2me | Theorems.Thm_FuchsThesis_HonestExpert_theorem_2_3
-- name    : FuchsThesis.HonestExpert.theorem_2_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T15:22:36.465752+00:00
-- url     : https://prove2.me/theorems/ffc4e8a3-d2c8-4d52-94a6-17f118a4d519
-- title:
--   Theorem 2.3 (Aczél) — only $\alpha\ln p+\gamma_k$ keeps the expert honest (corrected: $\alpha\ge 0$)
-- statement:
--   Let $n \ge 3$ and let $F_1, \dots, F_n$ be real-valued payoff functions. The honest-expert inequality
--
--   $$\sum_{k=1}^{n} p_k F_k(q_k) \;\le\; \sum_{k=1}^{n} p_k F_k(p_k) \qquad (2.47)$$
--
--   holds for all strictly positive $n$-point probability distributions $(p_1, \dots, p_n)$ and $(q_1, \dots, q_n)$ if and only if there exist constants $\alpha \ge 0$ and $\gamma_1, \dots, \gamma_n$ such that
--
--   $$F_k(p) = \alpha \ln p + \gamma_k \qquad \text{for all } k = 1, \dots, n \text{ and all } p \in (0, 1). \qquad (2.48)$$
--
--   In words: when there are at least three outcomes, the only payment schemes under which an expert maximizes his expected earnings by reporting his true probabilities are, up to a scale $\alpha \ge 0$ and outcome-dependent offsets $\gamma_k$, the logarithmic one. Plugging the logarithmic payoff into the expected loss of a dishonest report yields the Kullback–Leibler relative information $K(p_0/p_1) = \sum_b p_0(b) \ln(p_0(b)/p_1(b))$, (2.76), which is how the thesis derives it as a measure of distinguishability. For $n = 2$ the characterization fails (Muszély).
--
--   **Formalization Note** Distributions are strictly positive and (2.48) is asserted on $(0, 1)$, the set of values their coordinates take when $n \ge 3$; $\ln$ is `Real.log`; outcomes are indexed by `Fin n`.
--
--   Differences from the source:
--   - correction: there exist constants α and γ₁, …, γₙ → there exist α ≥ 0 and γ₁, …, γₙ; reason: the "if" direction is false for α < 0. Counterexample (n = 3, all assumptions met): α = −1, γ_k = 0, p = (½, ¼, ¼), q = (⅓, ⅓, ⅓) give Σ p_k F_k(q_k) = ln 3 ≈ 1.0986 > Σ p_k F_k(p_k) = (3/2) ln 2 ≈ 1.0397. The thesis's own proof derives α ≥ 0 ((2.67)–(2.68), p.23)
--   - reading: all n-point probability distributions, F_k : [0, 1] → ℝ, (2.48) on [0, 1] → all strictly positive n-point distributions, (2.48) for p ∈ (0, 1); reason: (2.48) is undefined at p = 0 for α ≠ 0, and with real values F_k(0) and distributions with zeros the only honest payoffs would be constants, contradicting the theorem's own "if" direction for α > 0; under this reading both directions hold and the proof's quantities p, q, r − p, r − q all lie in (0, 1)
--   - encoding: outcomes 1, …, n → Fin n; ln → Real.log; reason: Lean conventions
--   - encoding: real payoffs F_k defined on [0, 1] → real functions F_k defined on all of ℝ; reason: only values on (0, 1) enter (the coordinates of strictly positive distributions for n ≥ 3); any F_k on [0, 1] extends to ℝ and the extension changes no clause
-- source:
--   Fuchs, Distinguishability and Accessible Information in Quantum Theory, arXiv:quant-ph/9601020v1, §2.3.1, Theorem 2.3, eqs. (2.47)–(2.48), p.21 (PDF p.30); proof pp.21–24 (PDF pp.30–33)

import Mathlib
import Definitions.Def_FuchsThesis_HonestExpert_KeepsHonest

namespace FuchsThesis.HonestExpert

/-- **Theorem 2.3 (Aczél): only the logarithmic payoff keeps the expert honest
(corrected: `α ≥ 0`).**
Fuchs, *Distinguishability and Accessible Information in Quantum Theory*, arXiv:quant-ph/9601020v1,
§2.3.1, Theorem 2.3, eqs. (2.47)–(2.48), p.21 (PDF p.30): "Let n ≥ 3. Then the inequality
∑_{k=1}^n p_k F_k(q_k) ≤ ∑_{k=1}^n p_k F_k(p_k) (2.47) is satisfied for all n-point probability
distributions (p₁, …, pₙ) and (q₁, …, qₙ) if and only if there exist constants α and γ₁, …, γₙ such
that F_k(p) = α ln p + γ_k (2.48), for all k = 1, 2, …, n."

For `n ≥ 3` and payoff functions `F_k`, the inequality (2.47) holds for every pair of strictly
positive `n`-point distributions if and only if there are `α ≥ 0` and `γ₁, …, γₙ` with
`F_k(p) = α ln p + γ_k` for every `k` and every `p ∈ (0, 1)`.

**Correction.** The printed theorem lets `α` be any constant; the "if" direction fails for `α < 0`:
`n = 3`, `α = −1`, `γ_k = 0`, `p = (½, ¼, ¼)`, `q = (⅓, ⅓, ⅓)` give `∑ p_k F_k(q_k) = ln 3 ≈ 1.0986 >
∑ p_k F_k(p_k) = (3/2) ln 2 ≈ 1.0397`. The proof derives `α ≥ 0` ((2.67)–(2.68), p.23).

**Formalization Note.** Distributions are strictly positive (`KeepsHonest`, `IsPosDist`) and (2.48)
is asserted on `(0, 1)`, the set of values their coordinates take for `n ≥ 3`: the logarithm in
(2.48) is undefined at `0`. `ln` is `Real.log`. Outcomes are indexed by `Fin n`. -/
theorem theorem_2_3 {n : ℕ} (hn : 3 ≤ n) (F : Fin n → ℝ → ℝ) :
    KeepsHonest F ↔
      ∃ α : ℝ, 0 ≤ α ∧ ∃ γ : Fin n → ℝ, ∀ k, ∀ p ∈ Set.Ioo (0 : ℝ) 1,
        F k p = α * Real.log p + γ k := by sorry

end FuchsThesis.HonestExpert
