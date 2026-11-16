-- Prove2me | Theorems.Thm_LEDPCount_Supplement_theorem_5_3
-- name    : LEDPCount.Supplement.theorem_5_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T02:58:34.191741+00:00
-- url     : https://prove2.me/theorems/042eaae7-f261-4944-bcc7-d850ff81d73e
-- title:
--   Theorem 5.3 — every interactive $(\varepsilon,\delta)$-LEDP algorithm counting $H$ on $\mathcal G_{n,d}$ has error $\Omega(n^{q-1}d^{k-q-1}\min(n,\sqrt n/\varepsilon))$
-- statement:
--   Let $H$ be a pattern graph with $k$ vertices, $\ell\ge1$ edges and $q$ connected components, and let $f_H(G)$ denote the number of non-induced copies of $H$ in a graph $G$. Write $\mathcal G_{n,d}$ for the graphs on $[n]$ of maximum degree at most $d$. There exist constants $c,C,C_1,C_2>0$, depending only on $H$, such that the following holds for all $n,d\in\mathbb N$ with
--   $$
--   1\le d\le n-1,\qquad d\ge 6(k-2),
--   $$
--   all $\varepsilon\in(0,1]$, all $\alpha\in\bigl(0,\ n^{q}d^{k-q-1}/(3C)\bigr)$ and all
--   $$
--   \delta\in\Bigl[0,\ \frac{C_1\varepsilon^3\alpha^2}{n^{2q+1}d^{2k-2q-2}\,\ln\!\bigl(n^{2q+1}d^{2k-2q-2}/(C_2\varepsilon^2\alpha^2)\bigr)}\Bigr].
--   $$
--   If a (potentially fully interactive, with any number of rounds) local algorithm is $(\varepsilon,\delta)$-LEDP on $\mathcal G_{n,d}$ and, on every $G\in\mathcal G_{n,d}$, outputs an estimate $\hat f_H(G)$ with $\Pr[|\hat f_H(G)-f_H(G)|\le\alpha]\ge 2/3$, then
--   $$
--   \alpha\ \ge\ c\cdot n^{q-1}d^{k-q-1}\min\Bigl(n,\ \frac{\sqrt n}{\varepsilon}\Bigr)-\frac{n^{q-1}d^{k-q-1}}{C}.
--   $$
--
--   For $d=\Theta(n)$ and connected $H$ this is $\Omega(n^{k-3/2}/\varepsilon)$ (for $\varepsilon\ge 1/\sqrt n$), which matches the dependence on $n$ of the two-round upper bound $O(n^{k-3/2}/\varepsilon^{\ell})$ of Theorem 1.1: additional rounds of interaction cannot improve that dependence.
--
--   **Formalization Note** The algorithm class is `LEDPCount.Supplement.InteractiveLocal` (serialized interactive local model, arbitrary measurable choice and message spaces, any number of steps). The constants are chosen after $H$ and before $n,d,\varepsilon,\alpha,\delta$ and the algorithm. Exponents are integers.
--
--   Differences from the source:
--   - encoding: pattern graph H with k vertices, ℓ ≥ 1 edges and q connected components → H : SimpleGraph (Fin k), 1 ≤ H.edgeFinset.card, and a binder q with q = Nat.card H.ConnectedComponent; reason: Lean convention; isolated vertices count as components, as in the paper's proof of Claim 5.4
--   - encoding: (potentially interactive) (ε, δ)-LEDP algorithm in the round-based local model of §2.4 → InteractiveLocal n Ch M: serialized steps, each choice a Markov kernel of the transcript so far, selecting one party and an (ε', δ')-local randomizer (ε' > 0, δ' ∈ [0, 1)), with arbitrary measurable choice and message spaces Ch, M : Type; reason: a round selecting several parties is a run of consecutive steps whose choices ignore the in-round messages, and a step selecting one party is a round; the transcripts determine each other without using the data, so the classes coincide
--   - reading: LEDP algorithms may use an arbitrary number of rounds → for every T, every algorithm with T steps (T a field of the algorithm, chosen freely); reason: the complete transcript Π(x) is the transcript after the final round; an algorithm that stops early is padded with data-independent dummy steps
--   - encoding: the privacy parameters of each randomizer are specified by the algorithm and recorded → for every choice c there exist ε' > 0 and δ' ∈ [0, 1) for which the randomizer of c is an (ε', δ')-local randomizer; c itself is recorded; reason: the parameters are a function of the recorded choice; the theorem never uses their values
--   - reading: (ε, δ)-LEDP algorithm on G_{n,d} → the transcript law is (ε, δ)-DP for every edge-neighbouring pair G ∼ G' with both G and G' in G_{n,d}; reason: the algorithm's inputs are the graphs of G_{n,d}; this is the larger algorithm class, so the lower bound is the stronger one
--   - encoding: ε ∈ (0, 1], δ ∈ [0, …] → 0 < ε ≤ 1, 0 ≤ δ and δ < 1; reason: δ < 1 is the range of Definition 2.13, which the phrase (ε, δ)-LEDP presupposes
--   - encoding: δ ≤ C₁ε³α² / (n^{2q+1} d^{2k−2q−2} ln(n^{2q+1} d^{2k−2q−2}/(C₂ε²α²))) → the same bound with Real.log, plus the hypothesis 0 < log(n^{2q+1} d^{2k−2q−2}/(C₂ε²α²)); reason: where the logarithm is 0 the printed bound divides by zero and is undefined; where it is negative the printed interval for δ is empty, so nothing else is excluded
--   - encoding: exponents q, k − q − 1, q − 1, 2q + 1, 2k − 2q − 2 and 1 ≤ d ≤ n − 1, d ≥ 6(k − 2) → integer exponents (zpow on ℝ) and the comparisons d ≤ n − 1, 6(k − 2) ≤ d in ℤ; reason: no truncated subtraction; since ℓ ≥ 1 forces 1 ≤ q ≤ k − 1 and k ≥ 2, the exponents are the paper's natural numbers
--   - encoding: additive error at most α with probability at least 2/3 → for every G ∈ G_{n,d}, ENNReal.ofReal (2/3) ≤ (output law of A on G){y | |y − f_H(G)| ≤ α}, the output law being the output kernel composed with the transcript law; reason: Lean measure convention; the probability is over all coins of the algorithm
-- source:
--   Chen–Peng, The Power of Interaction in Locally Edge-Private Subgraph Counting, arXiv:2611.05038 (held version, sha256 d18032b0…), Theorem 5.3, p.56 (PDF p.58)

import Mathlib
import Definitions.Def_LEDPCount_subgraphCount
import Definitions.Def_LEDPCount_Supplement_boundedDegree
import Definitions.Def_LEDPCount_Supplement_InteractiveLocal

namespace LEDPCount.Supplement

open MeasureTheory

/-- Theorem 5.3 (Chen–Peng, *The Power of Interaction in Locally Edge-Private Subgraph Counting*,
arXiv:2611.05038, held version sha256 d18032b0…, §5, p.56, PDF p.58): for any pattern graph `H`
with `q` connected components, `k` vertices and `ℓ ≥ 1` edges there are constants
`c, C, C₁, C₂ > 0` such that for every `n, d ∈ ℕ` with `1 ≤ d ≤ n − 1` and `d ≥ 6(k − 2)`,
`ε ∈ (0, 1]`, `α ∈ (0, n^q d^{k−q−1}/(3C))` and
`δ ∈ [0, C₁ε³α² / (n^{2q+1} d^{2k−2q−2} ln(n^{2q+1} d^{2k−2q−2}/(C₂ε²α²)))]`, every (potentially
interactive) `(ε, δ)`-LEDP algorithm on `G_{n,d}` for `H`-counting with additive error at most `α`
with probability at least `2/3` must have
`α ≥ c · n^{q−1} d^{k−q−1} min(n, √n/ε) − n^{q−1} d^{k−q−1}/C`.

**Formalization Note** `H : SimpleGraph (Fin k)`; `q` is the number of connected components of `H`
(isolated vertices count), `ℓ = |E(H)|`. The constants are chosen after `H` and before
`n, d, ε, α, δ` and the algorithm. The algorithm class is `InteractiveLocal` (the paper's fully
interactive local model, serialized; arbitrary message and choice spaces, arbitrary number of
steps). LEDP is required for edge-neighbouring pairs inside `G_{n,d}` and accuracy for every graph in
`G_{n,d}`. `δ < 1` is the range of Definition 2.13. Exponents are integers (`zpow`); since `ℓ ≥ 1`
forces `1 ≤ q ≤ k − 1`, all of them are natural numbers, as in the paper. The hypothesis
`0 < ln(…)` excludes only the corner where the printed bound on `δ` divides by zero; where the
logarithm is negative the printed interval for `δ` is empty. -/
theorem theorem_5_3 {k : ℕ} (H : SimpleGraph (Fin k)) [DecidableRel H.Adj]
    (hℓ : 1 ≤ H.edgeFinset.card) (q : ℕ) (hq : q = Nat.card H.ConnectedComponent) :
    ∃ c C C₁ C₂ : ℝ, 0 < c ∧ 0 < C ∧ 0 < C₁ ∧ 0 < C₂ ∧
      ∀ (n d : ℕ) (ε α δ : ℝ),
        1 ≤ d → (d : ℤ) ≤ (n : ℤ) - 1 → 6 * ((k : ℤ) - 2) ≤ (d : ℤ) →
        0 < ε → ε ≤ 1 →
        0 < α → α < (n : ℝ) ^ (q : ℤ) * (d : ℝ) ^ ((k : ℤ) - q - 1) / (3 * C) →
        0 ≤ δ → δ < 1 →
        0 < Real.log ((n : ℝ) ^ (2 * (q : ℤ) + 1) * (d : ℝ) ^ (2 * (k : ℤ) - 2 * q - 2) /
          (C₂ * ε ^ 2 * α ^ 2)) →
        δ ≤ C₁ * ε ^ 3 * α ^ 2 /
          ((n : ℝ) ^ (2 * (q : ℤ) + 1) * (d : ℝ) ^ (2 * (k : ℤ) - 2 * q - 2) *
            Real.log ((n : ℝ) ^ (2 * (q : ℤ) + 1) * (d : ℝ) ^ (2 * (k : ℤ) - 2 * q - 2) /
              (C₂ * ε ^ 2 * α ^ 2))) →
        ∀ (Ch M : Type) [MeasurableSpace Ch] [MeasurableSpace M] (A : InteractiveLocal n Ch M),
          A.IsLEDPOn (boundedDegree n d) ε δ →
          A.CountsWithError H (boundedDegree n d) α →
          c * (n : ℝ) ^ ((q : ℤ) - 1) * (d : ℝ) ^ ((k : ℤ) - q - 1) *
              min (n : ℝ) (Real.sqrt n / ε) -
            (n : ℝ) ^ ((q : ℤ) - 1) * (d : ℝ) ^ ((k : ℤ) - q - 1) / C ≤ α := by sorry

end LEDPCount.Supplement
