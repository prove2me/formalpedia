-- Prove2me | Theorems.Thm_MultiphaseDisj_Supplement_theorem_A_6
-- name    : MultiphaseDisj.Supplement.theorem_A_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T07:35:46.223134+00:00
-- url     : https://prove2.me/theorems/8dc5084e-aab6-4a68-90a9-48a0e4a8d19c
-- title:
--   Theorem A.6 — streaming membership: $O(1)$ amortized, but $t_c=\Omega((\log M_n/\log(t_aw))^2)$ in the worst case
-- statement:
--   Let $\mathcal R_n := \{R_{\vec S} : S_1,\dots,S_n\subseteq[n]\}$ be the family of regular expressions encoding Disjointness (one branch $\#\,\Gamma_i^*\,c_i$ per set, over the alphabet $\#, a_1,\dots,a_n, c_1,\dots,c_n$), and let $M_n := \max_{R\in\mathcal R_n}|R|$. In streaming membership, an expression $R\in\mathcal R_n$ is preprocessed and a text arrives one symbol at a time; after each symbol the algorithm reports whether the text read so far belongs to $L(R)$. Then:
--
--   1. $M_n = \Theta(n^2)$.
--   2. Streaming membership for $\mathcal R_n$ has a deterministic algorithm with $O(1)$ amortized time per symbol on every input stream.
--   3. Consider any zero-error randomized cell-probe algorithm for streaming membership for all of $\mathcal R_n$, with word size $w=\Theta(\log M_n)$, arbitrary preprocessing of the given expression, and all information retained between symbols stored in memory. Let $t_a$ be its worst-case cost on a data symbol (over all expressions, texts and tapes) and $t_c$ an upper bound on its expected cost on a selector (for every expression and every text ending with this selector). Then
--   $$
--   t_c = \Omega\!\left(\left(\frac{\log M_n}{\log(t_a w)}\right)^{2}\right).
--   $$
--   4. In particular, the worst-case time $t$ on some symbol, for some expression in the family and some text, is
--   $$
--   t = \Omega\!\left(\left(\frac{\log M_n}{\log\log M_n}\right)^{2}\right).
--   $$
--
--   So amortized constant time is possible while every algorithm, even randomized, pays nearly $(\log M_n)^2$ in the worst case: an unconditional separation of amortized and worst-case time for a natural streaming problem.
--
--   **Formalization Note** Clause 1 reads $\Theta$ as $\exists\,0<c\le C$ with $cn^2\le M_n\le Cn^2$ for $n\ge1$, $|R|$ being the node count. Clause 2 gives one constant $C$ such that for every $n\ge1$ and every word size $w$ with $M_n\le 2^w$ a deterministic zero-error algorithm processes every text of length $L$ with total cost at most $CL$. Clauses 3 and 4 use the reading of the base goal `MultiphaseDisj.theorem_3_1`: for all $0<c_1\le c_2$ there are $C>0$ and $n_0$ such that the bounds hold with constant $C$ for all $n\ge n_0$, all $w\in[c_1\ln M_n, c_2\ln M_n]$, every tape probability space and every algorithm. Logarithms are natural; $t_a, t\in\mathbb N$ and $t_c\in\mathbb R$ are at least $1$.
--
--   Differences from the source:
--   - encoding: |R|, the length of a regular expression (no convention fixed) → size R, the node count of the syntax tree; reason: every standard length convention is within a constant factor of the node count, which changes only the constants of Θ(n²) and of the Ω bounds
--   - reading: a deterministic algorithm with O(1) amortized time per symbol (word size w = Θ(log M_n), polynomial space) → one constant C such that for every n ≥ 1 and every w with M_n ≤ 2^w there is a deterministic (tape Unit) zero-error algorithm whose total cost on every text of length L is at most C·L; reason: for w = c·log M_n with a small constant c the 2^w·w-bit memory cannot hold the n² bits of the sets, so the existence claim cannot be meant for every constant; the reading covers every w ≥ log₂ M_n, which contains the paper’s choice, and a uniform C is the O(1)
--   - reading: M_n = Θ(n²) → ∃ 0 < c, C with c·n² ≤ M_n ≤ C·n² for all n ≥ 1; reason: standard reading of Θ
--   - reading: w = Θ(log M_n), t_c = Ω((log M_n/log(t_a w))²), worst-case time Ω((log M_n/log log M_n)²) → for all 0 < c₁ ≤ c₂ there are C > 0 and n₀ such that for all n ≥ n₀, all w with c₁ ln M_n ≤ w ≤ c₂ ln M_n, every tape probability space and every algorithm, both bounds hold with constant C; reason: the quantified reading of the moderated base goal MultiphaseDisj.theorem_3_1; natural logarithms only change constants
--   - encoding: t_a its worst-case cost on a data symbol; t the worst-case time on all symbols → any natural numbers t_a, t ≥ 1 bounding these costs (DataCostLE, WorstCostLE); reason: the exact worst cases are instances; costs are normalized to be at least 1 (§2.1)
--   - encoding: t_c an upper bound on the expected cost on a selector → real t_c ≥ 1 with the probe count measurable in the tape and its lower Lebesgue integral at most t_c (ExpSelCostLE); reason: same convention as the base ExpQueryCostLE; costs normalized to be at least 1 (§2.1)
--   - encoding: a_1,…,a_n, c_1,…,c_n; random tape → Sym.data j, Sym.sel i with 0-based j, i : Fin n; tape any probability space (Ω, P), deterministic = Unit; reason: Lean conventions; same instances
-- source:
--   Ko, Unconditional Boolean Dynamic Lower Bounds from Disjointness, arXiv:2610.10904 (held version, sha256 ba26649b…), Theorem A.6, p.48 (family and costs: §A.7, pp.47–48; conventions: §2.1, p.11)

import Mathlib
import Definitions.Def_MultiphaseDisj_Supplement_StreamAlg

set_option autoImplicit false

open MeasureTheory

namespace MultiphaseDisj.Supplement

/-- **Theorem A.6 (Streaming membership: amortized versus worst case)** (Ko, *Unconditional
Boolean Dynamic Lower Bounds from Disjointness*, arXiv:2610.10904, held version sha256 ba26649b…,
Theorem A.6, p.48). Let `R_n := {R_S : S_1, …, S_n ⊆ [n]}` and `M_n := max_{R ∈ R_n} |R|`. Then

1. `M_n = Θ(n²)`;
2. streaming membership for `R_n` has a deterministic algorithm with `O(1)` amortized time per
   symbol on every input stream;
3. every zero-error cell-probe algorithm for streaming membership for all of `R_n`, with word size
   `w = Θ(log M_n)`, worst-case cost `ta` on a data symbol and expected cost at most `tc` on a
   selector, has `tc = Ω((log M_n / log(ta w))²)`;
4. in particular its worst-case time `t` on all symbols is `Ω((log M_n / log log M_n)²)`.

**Formalization Note** (1) is read as `∃ 0 < c, C` with `c n² ≤ M_n ≤ C n²` for all `n ≥ 1`,
with `|R|` the node count of the syntax tree (`size`). (2) is read as: there is one constant `C`
such that for every `n ≥ 1` and every word size `w` with `M_n ≤ 2^w` (i.e. `w ≥ log₂ M_n`) a
deterministic (`Ω = Unit`) zero-error algorithm has total cost at most `C · L` on every text of
length `L`; the reading of `w = Θ(log M_n)` for this existence claim is that `w` is at least
`log₂ M_n`, since with `w = c log M_n` for a small `c` the memory cannot hold the sets at all.
(3) and (4) use the reading of `Θ`/`Ω` of the base goal `MultiphaseDisj.theorem_3_1`: for all
constants `0 < c₁ ≤ c₂` there are `C > 0` and `n₀` such that for every `n ≥ n₀`, every `w` with
`c₁ ln M_n ≤ w ≤ c₂ ln M_n`, every tape probability space and every algorithm, both bounds hold
with constant `C`. Logarithms are natural; `ta, t ∈ ℕ` and `tc ∈ ℝ` are upper bounds on the
costs, normalized to be at least `1` (§2.1). Correctness and costs are over all texts. -/
theorem theorem_A_6 :
    (∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
        c * (n : ℝ) ^ 2 ≤ (Mn n : ℝ) ∧ (Mn n : ℝ) ≤ C * (n : ℝ) ^ 2) ∧
    (∃ C : ℕ, ∀ n : ℕ, 1 ≤ n → ∀ w : ℕ, Mn n ≤ 2 ^ w →
        ∃ A : StreamAlg n n w Unit, A.ZeroError ∧ A.AmortizedCostLE C) ∧
    (∀ c₁ c₂ : ℝ, 0 < c₁ → c₁ ≤ c₂ → ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∀ w : ℕ, c₁ * Real.log (Mn n) ≤ w → (w : ℝ) ≤ c₂ * Real.log (Mn n) →
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (A : StreamAlg n n w Ω), A.ZeroError →
        (∀ (ta : ℕ) (tc : ℝ), 1 ≤ ta → 1 ≤ tc → A.DataCostLE ta → A.ExpSelCostLE P tc →
          C * (Real.log (Mn n) / Real.log ((ta : ℝ) * w)) ^ 2 ≤ tc) ∧
        (∀ t : ℕ, 1 ≤ t → A.WorstCostLE t →
          C * (Real.log (Mn n) / Real.log (Real.log (Mn n))) ^ 2 ≤ t)) := by sorry

end MultiphaseDisj.Supplement
