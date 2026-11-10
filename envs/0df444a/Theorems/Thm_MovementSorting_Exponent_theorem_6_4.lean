-- Prove2me | Theorems.Thm_MovementSorting_Exponent_theorem_6_4
-- name    : MovementSorting.Exponent.theorem_6_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T21:03:56.222396+00:00
-- url     : https://prove2.me/theorems/85ca3e1c-d7e5-4d7d-876a-b8ce431ed698
-- title:
--   Theorem 6.4 — Algorithm 3 sorts in 3 rounds with expected movement O_d(n^{β^{(d)}_3})
-- statement:
--   For every $d \ge 2$: $\beta^{(d)}_3 = (16d^2-6d+1)/(12d^2-6d+1)$; for every route constant $C_R$ there are $C > 0$ and $m_0$ such that for every $m \ge m_0$ and every admissible family of route procedures, Algorithm 3 (splitters, then a cube sample of side $H$ at rate $p$ and a key sample at rate $\sigma$, then the cleanup) is correct for every outcome of its coins and has expected movement at most $C n^{\beta^{(d)}_3}$ on every input; hence $M^{(d)}_3(n) \le C' n^{\beta^{(d)}_3}$ for $m \ge m_0'$, with $C'$ depending only on $d$. Admissible route families exist with one positive route constant uniform in $m \ge 2$ (depending only on the fixed dimension and round budget).
--
--   Differences from the source:
--   - generalization: Algorithm 3 with the route procedures the paper specifies → Algorithm 3 with its splitters, samples, rates and required configurations exactly as in the paper, and ANY route procedures admissible with a constant CR (valid routes from the current configuration visiting every required configuration, with movement at most CR times the per-instance quantity bounded in the proofs of Lemma 6.3 and Theorem 6.4 (with Lemma 5.1)); the conclusion holds for every CR with C depending on CR; existence of an admissible family with one positive CR uniform in m ≥ 2 is also asserted; reason: Algorithm 1 is a template (pp. 25–26). The source constructs routes with the stated per-instance bounds; their existence is retained explicitly, and the universal clause also covers any other procedures satisfying those bounds. Thus the generalized theorem includes the source algorithm and is not only a conditional bound.
--   - encoding: correct for every outcome of its coins; expected movement on every input → IsValidAlg of the deterministic algorithm fixed by every coin outcome in the support of Plan.coins (uniform splitter set of size ⌈n/b₀⌉, independent box selections), and Plan.expMove (Σ over coin outcomes) bounded for every π; reason: the sampling of Algorithm 1 written as a PMF; rates are clamped to [0, 1] only to make the coin total, and the instance rates lie in (0, 1)
--   - encoding: asymptotic symbols Ω / O / Θ with the stated subscripts, n → ∞ → explicit constants (c > 0 or C > 0) quantified with exactly the stated dependencies, and a threshold m₀ with the bound for every m ≥ m₀, n = m^d (nR d m); reason: the model is defined only at n = m^d; the constants are uniform in m as the notation of p. 8 requires
--   - encoding: M^{(d)}_r(n) = inf_ALG max_π E[Move(ALG, π)] over randomized r-round algorithms correct for every input and coin outcome → M d r m ∈ ℝ≥0∞: ⨅ over PMFs on valid (well-formed, correct) deterministic r-round algorithms of ⨆ over inputs π of Σ μ(A)·Move(A, π); Minf d m = ⨅ over r ≥ 1; reason: Definition 2.1 with the coins fixed in advance; ℝ≥0∞ makes the infimum over an empty class +∞ instead of a junk 0, and countable-support coin distributions are the paper's algorithms
-- source:
--   Wang (2026), The Movement Complexity of Sorting, arXiv:2611.01157 (held copy SHA-256 90e3d9df…), Theorem 6.4, p. 31

import Definitions.Def_MovementSorting_Exponent_Algorithms

set_option autoImplicit false

namespace MovementSorting.Exponent

/-- Theorem 6.4 (p. 31): for every `d ≥ 2`, Algorithm 3 (here with any admissible route
procedures, constant `CR`) sorts with expected movement `O_d(n^{β^{(d)}_3})` on every input,
correct for every outcome of its coins, where `β^{(d)}_3 = (16d²-6d+1)/(12d²-6d+1)`; hence
`M^{(d)}_3(n) = O_d(n^{β^{(d)}_3})`. Admissible procedures exist with one constant uniform in `m`. -/
theorem theorem_6_4 :
    ∀ d : ℕ, 2 ≤ d →
      beta d 3 = (16 * d ^ 2 - 6 * d + 1 : ℝ) / (12 * d ^ 2 - 6 * d + 1) ∧
      (∃ CR : ℝ, 0 < CR ∧ ∀ m : ℕ, 2 ≤ m →
        ∃ procs : Coins d m → ℕ → RouteProc d m, Alg3Admissible d m CR procs) ∧
      (∀ CR : ℝ, ∃ C : ℝ, 0 < C ∧ ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m →
        ∀ procs : Coins d m → ℕ → RouteProc d m, Alg3Admissible d m CR procs →
          (∀ ω ∈ (alg3Plan d m).coins.support, IsValidAlg ((alg3Plan d m).alg procs ω)) ∧
          ∀ π : Input d m, (alg3Plan d m).expMove procs π ≤ ENNReal.ofReal (C * nR d m ^ beta d 3)) ∧
      (∃ C : ℝ, 0 < C ∧ ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m →
        M d 3 m ≤ ENNReal.ofReal (C * nR d m ^ beta d 3)) := by sorry

end MovementSorting.Exponent
