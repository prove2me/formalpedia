-- Prove2me | Theorems.Thm_MovementSorting_Exponent_theorem_5_11
-- name    : MovementSorting.Exponent.theorem_5_11
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T21:03:48.001611+00:00
-- url     : https://prove2.me/theorems/42830ae7-8dee-4b00-9c14-7a4685e3b4cd
-- title:
--   Theorem 5.11 — on the line, r rounds sort with expected movement O_r(n^{β_r}) (Algorithm 2 for r ≥ 2)
-- statement:
--   For $d = 1$: for $r = 1$ there are $C$ and $m_0$ such that for every $m \ge m_0$ some $1$-round (randomized, correct for every coin outcome) algorithm has $\max_\pi E[\mathrm{Move}] \le C n^{\beta_1}$. For every $r \ge 2$ and every route constant $C_R$ there are $C > 0$ and $m_0$ such that for every $m \ge m_0$ and every admissible family of route procedures, Algorithm 2 (splitters, interval samples of length $h_j$ at rate $p_j$) is correct for every outcome of its coins and has expected movement at most $C n^{\beta_r}$ on every input. Admissible route families exist with one positive route constant uniform in $m \ge 2$ (depending only on the fixed dimension and round budget).
--
--   Differences from the source:
--   - generalization: Algorithm 2 with the route procedures the paper specifies → Algorithm 2 with its splitters, samples, rates and required configurations exactly as in the paper, and ANY route procedures admissible with a constant CR (valid routes from the current configuration visiting every required configuration, with movement at most CR times the per-instance quantity bounded in the proofs of Lemmas 5.9 and 5.10); the conclusion holds for every CR with C depending on CR; existence of an admissible family with one positive CR uniform in m ≥ 2 is also asserted; reason: Algorithm 1 is a template (pp. 25–26). The source constructs routes with the stated per-instance bounds; their existence is retained explicitly, and the universal clause also covers any other procedures satisfying those bounds. Thus the generalized theorem includes the source algorithm and is not only a conditional bound.
--   - encoding: correct for every outcome of its coins; expected movement on every input → IsValidAlg of the deterministic algorithm fixed by every coin outcome in the support of Plan.coins (uniform splitter set of size ⌈n/b₀⌉, independent box selections), and Plan.expMove (Σ over coin outcomes) bounded for every π; reason: the sampling of Algorithm 1 written as a PMF; rates are clamped to [0, 1] only to make the coin total, and the instance rates lie in (0, 1)
--   - encoding: "an r-round algorithm" for r = 1 (the proof gives a deterministic serpentine route) → ∃ μ : RandAlg 1 m 1 with expMove μ π ≤ C n^{β_1} for every π; reason: the statement asserts an r-round algorithm, randomized in general; a deterministic one is a Dirac PMF
--   - encoding: asymptotic symbols Ω / O / Θ with the stated subscripts, n → ∞ → explicit constants (c > 0 or C > 0) quantified with exactly the stated dependencies, and a threshold m₀ with the bound for every m ≥ m₀, n = m^d (nR d m); reason: the model is defined only at n = m^d; the constants are uniform in m as the notation of p. 8 requires
-- source:
--   Wang (2026), The Movement Complexity of Sorting, arXiv:2611.01157 (held copy SHA-256 90e3d9df…), Theorem 5.11, p. 28

import Definitions.Def_MovementSorting_Exponent_Algorithms

set_option autoImplicit false

namespace MovementSorting.Exponent

/-- Theorem 5.11 (p. 28): for every fixed `r`, an `r`-round algorithm sorts the line (`d = 1`)
with expected movement `O_r(n^{β_r})` on every input, correct for every outcome of its coins; for
`r ≥ 2` it is Algorithm 2 (here with any admissible route procedures, constant `CR`).
Such procedures exist with one constant uniform in `m`. -/
theorem theorem_5_11 :
    (∃ C : ℝ, 0 < C ∧ ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m →
      ∃ μ : RandAlg 1 m 1, ∀ π : Input 1 m, expMove μ π ≤ ENNReal.ofReal (C * nR 1 m ^ beta 1 1)) ∧
    (∀ r : ℕ, 2 ≤ r →
      (∃ CR : ℝ, 0 < CR ∧ ∀ m : ℕ, 2 ≤ m →
        ∃ procs : Coins 1 m → ℕ → RouteProc 1 m, Alg2Admissible r m CR procs) ∧
      (∀ CR : ℝ, ∃ C : ℝ, 0 < C ∧ ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m →
      ∀ procs : Coins 1 m → ℕ → RouteProc 1 m, Alg2Admissible r m CR procs →
        (∀ ω ∈ (alg2Plan r m).coins.support, IsValidAlg ((alg2Plan r m).alg procs ω)) ∧
        ∀ π : Input 1 m, (alg2Plan r m).expMove procs π ≤ ENNReal.ofReal (C * nR 1 m ^ beta 1 r))) := by sorry

end MovementSorting.Exponent
