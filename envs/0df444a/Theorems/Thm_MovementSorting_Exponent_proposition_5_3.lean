-- Prove2me | Theorems.Thm_MovementSorting_Exponent_proposition_5_3
-- name    : MovementSorting.Exponent.proposition_5_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T21:01:27.107773+00:00
-- url     : https://prove2.me/theorems/18f9b2cb-6405-4b0c-b146-e45ddb9dabf6
-- title:
--   Proposition 5.3 — a deterministic merge sort in O((log n)³) rounds with movement O_d(n^{1+1/(2d)})
-- statement:
--   There is an absolute constant $C' > 0$ such that for every $d \ge 1$ there are $C > 0$ and $m_0$ such that for every $m \ge m_0$ some valid deterministic algorithm with $R \le C'(\log_2 n)^3$ rounds has movement at most $C n^{1+1/(2d)}$ on every input; hence $M^{(d)}_\infty(n) \le C n^{1+1/(2d)}$.
--
--   Differences from the source:
--   - encoding: asymptotic symbols Ω / O / Θ with the stated subscripts, n → ∞ → explicit constants (c > 0 or C > 0) quantified with exactly the stated dependencies, and a threshold m₀ with the bound for every m ≥ m₀, n = m^d (nR d m); reason: the model is defined only at n = m^d; the constants are uniform in m as the notation of p. 8 requires
--   - encoding: M^{(d)}_r(n) = inf_ALG max_π E[Move(ALG, π)] over randomized r-round algorithms correct for every input and coin outcome → M d r m ∈ ℝ≥0∞: ⨅ over PMFs on valid (well-formed, correct) deterministic r-round algorithms of ⨆ over inputs π of Σ μ(A)·Move(A, π); Minf d m = ⨅ over r ≥ 1; reason: Definition 2.1 with the coins fixed in advance; ℝ≥0∞ makes the infimum over an empty class +∞ instead of a junk 0, and countable-support coin distributions are the paper's algorithms
--   - encoding: log n (base 2) → Real.logb 2 (nR d m); reason: the paper fixes base 2 (p. 8); n ≥ 2 so the logarithm is positive
--   - encoding: "a deterministic algorithm sorts in O((log n)^3) rounds" → for each m ≥ m₀ some R ≤ C′ log₂³ n and a valid A : DetAlg d m R; C′ absolute; reason: an algorithm of the model is defined per n (Definition 2.1); O without subscript hides an absolute constant (p. 8)
-- source:
--   Wang (2026), The Movement Complexity of Sorting, arXiv:2611.01157 (held copy SHA-256 90e3d9df…), Proposition 5.3, p. 24

import Definitions.Def_MovementSorting_Exponent_Model

set_option autoImplicit false

namespace MovementSorting.Exponent

/-- Proposition 5.3 (p. 24): for every `d ≥ 1`, a deterministic algorithm sorts in
`O((log n)^3)` rounds (absolute constant) with movement `O_d(n^{1+1/(2d)})`; hence
`M^{(d)}_∞(n) = O_d(n^{1+1/(2d)})`. -/
theorem proposition_5_3 :
    ∃ C' : ℝ, 0 < C' ∧ ∀ d : ℕ, 1 ≤ d → ∃ C : ℝ, 0 < C ∧ ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m →
      (∃ R : ℕ, (R : ℝ) ≤ C' * Real.logb 2 (nR d m) ^ 3 ∧
        ∃ A : DetAlg d m R, IsValidAlg A ∧
          ∀ π : Input d m, (A.move π : ℝ) ≤ C * nR d m ^ (1 + 1 / (2 * d : ℝ))) ∧
      Minf d m ≤ ENNReal.ofReal (C * nR d m ^ (1 + 1 / (2 * d : ℝ))) := by sorry

end MovementSorting.Exponent
