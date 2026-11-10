-- Prove2me | Theorems.Thm_MovementSorting_Exponent_theorem_6_11
-- name    : MovementSorting.Exponent.theorem_6_11
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T21:03:51.664681+00:00
-- url     : https://prove2.me/theorems/e503c5a0-624a-4d4a-b6a2-7c5fda682be3
-- title:
--   Theorem 6.11 — Algorithm 4 sorts with expected movement O_{d,r}(n^{β^{(d)}_r} log² n) for d ≥ 2, r ≥ 4
-- statement:
--   For every $d \ge 2$ and $r \ge 4$, and every route constant $C_R$, there are $C > 0$ and $m_0$ such that for every $m \ge m_0$ and every admissible family of route procedures, Algorithm 4 (splitters, then per refinement round one sample at every dyadic spatial scale $y \le x_\star$ at rate $n^{-f_j(y)}$, then the cleanup) is correct for every outcome of its coins and has expected movement at most $C n^{\beta^{(d)}_r}\log_2^2 n$ on every input; hence $M^{(d)}_r(n) \le C' n^{\beta^{(d)}_r}\log_2^2 n$ for $m \ge m_0'$, with $C'$ depending only on $d$ and $r$. Admissible route families exist with one positive route constant uniform in $m \ge 2$ (depending only on the fixed dimension and round budget).
--
--   Differences from the source:
--   - generalization: Algorithm 4 with the route procedures the paper specifies → Algorithm 4 with its splitters, samples, rates and required configurations exactly as in the paper, and ANY route procedures admissible with a constant CR (valid routes from the current configuration visiting every required configuration, with movement at most CR times the per-instance quantity bounded in Lemma 6.6 (routes of Lines 4 and 7)); the conclusion holds for every CR with C depending on CR; existence of an admissible family with one positive CR uniform in m ≥ 2 is also asserted; reason: Algorithm 1 is a template (pp. 25–26). The source constructs routes with the stated per-instance bounds; their existence is retained explicitly, and the universal clause also covers any other procedures satisfying those bounds. Thus the generalized theorem includes the source algorithm and is not only a conditional bound.
--   - encoding: correct for every outcome of its coins; expected movement on every input → IsValidAlg of the deterministic algorithm fixed by every coin outcome in the support of Plan.coins (uniform splitter set of size ⌈n/b₀⌉, independent box selections), and Plan.expMove (Σ over coin outcomes) bounded for every π; reason: the sampling of Algorithm 1 written as a PMF; rates are clamped to [0, 1] only to make the coin total, and the instance rates lie in (0, 1)
--   - encoding: asymptotic symbols Ω / O / Θ with the stated subscripts, n → ∞ → explicit constants (c > 0 or C > 0) quantified with exactly the stated dependencies, and a threshold m₀ with the bound for every m ≥ m₀, n = m^d (nR d m); reason: the model is defined only at n = m^d; the constants are uniform in m as the notation of p. 8 requires
--   - encoding: M^{(d)}_r(n) = inf_ALG max_π E[Move(ALG, π)] over randomized r-round algorithms correct for every input and coin outcome → M d r m ∈ ℝ≥0∞: ⨅ over PMFs on valid (well-formed, correct) deterministic r-round algorithms of ⨆ over inputs π of Σ μ(A)·Move(A, π); Minf d m = ⨅ over r ≥ 1; reason: Definition 2.1 with the coins fixed in advance; ℝ≥0∞ makes the infimum over an empty class +∞ instead of a junk 0, and countable-support coin distributions are the paper's algorithms
--   - encoding: log n (base 2) → Real.logb 2 (nR d m); reason: the paper fixes base 2 (p. 8); n ≥ 2 so the logarithm is positive
-- source:
--   Wang (2026), The Movement Complexity of Sorting, arXiv:2611.01157 (held copy SHA-256 90e3d9df…), Theorem 6.11, p. 35

import Definitions.Def_MovementSorting_Exponent_Algorithms

set_option autoImplicit false

namespace MovementSorting.Exponent

/-- Theorem 6.11 (p. 35): for every fixed `d ≥ 2` and `r ≥ 4`, Algorithm 4 (here with any
admissible route procedures, constant `CR`) sorts with expected movement
`O_{d,r}(n^{β^{(d)}_r} log² n)` on every input, correct for every outcome of its coins; hence
`M^{(d)}_r(n) = O_{d,r}(n^{β^{(d)}_r} log² n)`. Admissible procedures exist with one constant
uniform in `m`. -/
theorem theorem_6_11 :
    ∀ d r : ℕ, 2 ≤ d → 4 ≤ r →
      (∃ CR : ℝ, 0 < CR ∧ ∀ m : ℕ, 2 ≤ m →
        ∃ procs : Coins d m → ℕ → RouteProc d m, Alg4Admissible d r m CR procs) ∧
      (∀ CR : ℝ, ∃ C : ℝ, 0 < C ∧ ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m →
        ∀ procs : Coins d m → ℕ → RouteProc d m, Alg4Admissible d r m CR procs →
          (∀ ω ∈ (alg4Plan d r m).coins.support, IsValidAlg ((alg4Plan d r m).alg procs ω)) ∧
          ∀ π : Input d m, (alg4Plan d r m).expMove procs π ≤
            ENNReal.ofReal (C * nR d m ^ beta d r * Real.logb 2 (nR d m) ^ 2)) ∧
      (∃ C : ℝ, 0 < C ∧ ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m →
        M d r m ≤ ENNReal.ofReal (C * nR d m ^ beta d r * Real.logb 2 (nR d m) ^ 2)) := by sorry

end MovementSorting.Exponent
