-- Prove2me | Theorems.Thm_HypClass1_proposition_9_3
-- name    : HypClass1.proposition_9_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T07:33:23.91346+00:00
-- url     : https://prove2.me/theorems/4ac943e5-b33f-4933-89c0-9627491182a4
-- title:
--   Proposition 9.3 — the exposure probabilities $q_1,\dots,q_{2t}$ of (34) exist
-- statement:
--   Let $\alpha \in (0,1)$, let $n$ be sufficiently large, let $n^{-1+\alpha} \le p \le 0.99$, and let $k$ and $t$ be integers with
--   $$
--   k = \lfloor n^{\alpha/1000} \rfloor \quad\text{and}\quad n^{-1+\alpha/3} \le p k^{-t/4} \le n^{-1+\alpha/2}. \tag{33}
--   $$
--   Consider real numbers $q_1, \dots, q_{2t} \in (0,1)$ with
--   $$
--   1 - p = \prod_{i=1}^{2t} (1 - q_i), \qquad q_2 = k^{-8} q_1, \qquad q_i = \begin{cases} 2 q_{i-1}, & i \ge 3 \text{ odd},\\ k^{-1/4} q_{i-1}, & i \ge 3 \text{ even}. \end{cases} \tag{34}
--   $$
--   Then such a choice exists, and every such choice satisfies
--   $$
--   (1 - 4k^{-8})p \le q_1 \le p \qquad\text{and}\qquad n^{-1+\alpha/4} \le q_{2t} \le n^{-1+\alpha/2}.
--   $$
--
--   These are the probabilities of the $2t$ rounds in which $H^{(3)}_{n,p}$ is exposed in the proof of Lemma 9.2.
--
--   **Formalization Note** $n_0$ depends on $\alpha$; $q$ is a sequence indexed by $\mathbb N$ and only $q_1, \dots, q_{2t}$ matter. Powers of $k$ are real powers.
--
--   Differences from the source:
--   - reading: Proposition 9.3 is stated in the setting of §9.1 (Lemma 9.2: α ∈ (0,1), n^{−1+α} ≤ p ≤ 0.99) with k, t 'integers chosen such that' (33); its proof uses that k is sufficiently large → ∀ α ∈ (0,1), ∃ n₀, ∀ n ≥ n₀, ∀ p ∈ [n^{−1+α}, 0.99], ∀ t : ℕ satisfying (33); reason: these are the standing assumptions of the section the proposition belongs to
-- source:
--   Chatterjee, Ferber, Sales, Shurman, Almost Every 3-Uniform Hypergraph is Class 1, manuscript (STOC 2027 submission, version of 2026-11-03, sha256 ce3bba9d…), Proposition 9.3, p.48, with (33)–(34), p.47

import Mathlib

namespace HypClass1

/-- **Proposition 9.3 (the exposure probabilities (34) exist).** Chatterjee, Ferber, Sales, Shurman, *Almost Every 3-Uniform Hypergraph is Class 1*, manuscript
(STOC 2027 submission, version of 2026-11-03, sha256 ce3bba9d…), Proposition 9.3, p.48, with the
setting (33)–(34), p.47: "Let k and t be integers chosen such that k := ⌊n^{α/1000}⌋ and
n^{−1+α/3} ≤ pk^{−t/4} ≤ n^{−1+α/2}. (33) Moreover, let {q_i}_{1≤i≤2t} be real numbers in (0, 1) chosen
such that 1 − p = Π_{i=1}^{2t}(1 − q_i), q₂ = k^{−8}q₁ and q_i = 2q_{i−1} if i ≥ 3 is odd, k^{−1/4}q_{i−1} if
i ≥ 3 is even. (34)" — "There exists a choice of {q_i}_{1≤i≤2t} satisfying (34). Moreover, for any such
choice it holds that (1 − 4k^{−8})p ≤ q₁ ≤ p, and n^{−1+α/4} ≤ q_{2t} ≤ n^{−1+α/2}."

**Formalization Note.** The standing setting of §9 (Lemma 9.2): `α ∈ (0, 1)`, `n^{−1+α} ≤ p ≤ 0.99`, `n`
sufficiently large (`∃ n₀` depending on `α`), and `t` any natural number satisfying (33). Both clauses
(existence; bounds for every choice) are stated. The sequence `q` is indexed by `ℕ` and only its values
at `1, …, 2t` matter. -/
theorem proposition_9_3 (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ p : ℝ, (n : ℝ) ^ (-1 + α) ≤ p → p ≤ 0.99 → ∀ t : ℕ,
      (n : ℝ) ^ (-1 + α / 3) ≤ p * ((⌊(n : ℝ) ^ (α / 1000)⌋₊ : ℕ) : ℝ) ^ (-(t : ℝ) / 4) →
      p * ((⌊(n : ℝ) ^ (α / 1000)⌋₊ : ℕ) : ℝ) ^ (-(t : ℝ) / 4) ≤ (n : ℝ) ^ (-1 + α / 2) →
      (∃ q : ℕ → ℝ, (∀ i, 1 ≤ i → i ≤ 2 * t → 0 < q i ∧ q i < 1) ∧
          1 - p = ∏ i ∈ Finset.Icc 1 (2 * t), (1 - q i) ∧
          q 2 = ((⌊(n : ℝ) ^ (α / 1000)⌋₊ : ℕ) : ℝ) ^ (-8 : ℝ) * q 1 ∧
          (∀ i, 3 ≤ i → i ≤ 2 * t →
            (Odd i → q i = 2 * q (i - 1)) ∧
            (Even i → q i = ((⌊(n : ℝ) ^ (α / 1000)⌋₊ : ℕ) : ℝ) ^ (-1 / 4 : ℝ) * q (i - 1)))) ∧
      (∀ q : ℕ → ℝ, (∀ i, 1 ≤ i → i ≤ 2 * t → 0 < q i ∧ q i < 1) →
          1 - p = ∏ i ∈ Finset.Icc 1 (2 * t), (1 - q i) →
          q 2 = ((⌊(n : ℝ) ^ (α / 1000)⌋₊ : ℕ) : ℝ) ^ (-8 : ℝ) * q 1 →
          (∀ i, 3 ≤ i → i ≤ 2 * t →
            (Odd i → q i = 2 * q (i - 1)) ∧
            (Even i → q i = ((⌊(n : ℝ) ^ (α / 1000)⌋₊ : ℕ) : ℝ) ^ (-1 / 4 : ℝ) * q (i - 1))) →
          (1 - 4 * ((⌊(n : ℝ) ^ (α / 1000)⌋₊ : ℕ) : ℝ) ^ (-8 : ℝ)) * p ≤ q 1 ∧ q 1 ≤ p ∧
          (n : ℝ) ^ (-1 + α / 4) ≤ q (2 * t) ∧ q (2 * t) ≤ (n : ℝ) ^ (-1 + α / 2)) := by sorry

end HypClass1
